/*
 * sbt
 * Copyright 2011 - 2017, Lightbend, Inc.
 * Copyright 2008 - 2010, Mark Harrah
 * Licensed under BSD-3-Clause license (see LICENSE)
 */

package sbt
package lsp

import sbt.internal.inc.MixedAnalyzingCompiler
import sbt.internal.langserver.ErrorCodes
import sbt.util.Logger
import scala.annotation.tailrec
import scala.concurrent.{ ExecutionContext, Future }
import scala.util.matching.Regex.MatchIterator
import java.nio.file.Paths
import xsbti.compile.AnalysisStore

object Definition {
  import java.net.URI
  import Keys._
  import sbt.internal.inc.Analysis
  import sbt.internal.inc.JavaInterfaceUtil._
  val AnalysesKey = "lsp.definition.analyses.key"

  import sjsonnew.JsonFormat
  def send[A: JsonFormat](source: CommandSource, execId: String)(params: A): Unit = {
    for {
      channel <- StandardMain.exchange.channels.collectFirst {
        case c if c.name == source.channelName => c
      }
    } yield {
      channel.publishEvent(params, Option(execId))
    }
  }

  object textProcessor {
    private val isIdentifier = {
      import scala.tools.reflect.{ ToolBox, ToolBoxError }
      lazy val tb =
        scala.reflect.runtime.universe
          .runtimeMirror(this.getClass.getClassLoader)
          .mkToolBox()
      import tb._
      lazy val check = parse _ andThen compile _
      (identifier: String) =>
        try {
          check(s"val $identifier = 0; val ${identifier}${identifier} = $identifier")
          true
        } catch {
          case _: ToolBoxError => false
        }
    }

    def identifier(line: String, point: Int): Option[String] = {
      val whiteSpaceReg = "\\s+".r
      val (zero, end) = fold(Seq.empty)(whiteSpaceReg.findAllIn(line))
        .collect {
          case (white, ind) => (ind, ind + white.length)
        }
        .fold((0, line.length)) { (z, e) =>
          val (from, to) = e
          val (left, right) = z
          (if (to > left && to <= point) to else left,
           if (from < right && from >= point) from else right)
        }
      val ranges = for {
        from <- zero to point
        to <- point to end
      } yield (from -> to)
      val potentials = ranges.par
        .collect {
          case (from, to) => line.slice(from, to).trim
        }
        .collect {
          case fragment if fragment.nonEmpty && isIdentifier(fragment) => fragment
        }
        .seq
      potentials match {
        case Nil        => None
        case potentials => Some(potentials.maxBy(_.length))
      }
    }

    private def asClassObjectIdentifier(sym: String) =
      Seq(s".$sym", s".$sym$$", s"$$$sym", s"$$$sym$$")
    def potentialClsOrTraitOrObj(sym: String): PartialFunction[String, String] = {
      case potentialClassOrTraitOrObject
          if asClassObjectIdentifier(sym).exists(potentialClassOrTraitOrObject.endsWith) ||
            sym == potentialClassOrTraitOrObject ||
            s"$sym$$" == potentialClassOrTraitOrObject =>
        potentialClassOrTraitOrObject
    }

    @tailrec
    private def fold(z: Seq[(String, Int)])(it: MatchIterator): Seq[(String, Int)] = {
      if (!it.hasNext) z
      else fold(z :+ (it.next() -> it.start))(it)
    }

    private[lsp] def classTraitObjectInLine(sym: String)(line: String): Seq[(String, Int)] = {
      val potentials =
        Seq(s"object +$sym".r, s"trait +$sym *\\[?".r, s"class +$sym *\\[?".r)
      potentials
        .flatMap { reg =>
          fold(Seq.empty)(reg.findAllIn(line))
        }
        .collect {
          case (name, pos) =>
            (if (name.endsWith("[")) name.init.trim else name.trim) -> pos
        }
    }

    import java.io.File
    def markPosition(file: File, sym: String): Seq[(File, Int, Int, Int)] = {
      import java.nio.file._
      import scala.collection.JavaConverters._
      val findInLine = classTraitObjectInLine(sym)(_)
      Files
        .lines(file.toPath)
        .iterator
        .asScala
        .zipWithIndex
        .flatMap {
          case (line, lineNumber) =>
            findInLine(line)
              .collect {
                case (sym, from) =>
                  (file, lineNumber, from, from + sym.length)
              }
        }
        .toSeq
        .distinct
    }
  }

  import sbt.internal.langserver.TextDocumentPositionParams
  import sjsonnew.shaded.scalajson.ast.unsafe.JValue
  private def getDefinition(jsonDefinition: JValue): Option[TextDocumentPositionParams] = {
    import sbt.internal.langserver.codec.JsonProtocol._
    import sjsonnew.support.scalajson.unsafe.Converter
    Converter.fromJson[TextDocumentPositionParams](jsonDefinition).toOption
  }

  import scalacache._
  private[sbt] def updateCache[F[_]](cache: Cache[Any])(cacheFile: String, useBinary: Boolean)(
      implicit
      mode: Mode[F],
      flags: Flags): F[Any] = {
    import scala.concurrent.duration.Duration.Inf
    mode.M.flatMap(cache.get(AnalysesKey)) {
      case None =>
        cache.put(AnalysesKey)(
          Set(
            cacheFile -> MixedAnalyzingCompiler.staticCachedStore(Paths.get(cacheFile).toFile,
                                                                  !useBinary)),
          Option(Inf))
      case Some(set) =>
        cache.put(AnalysesKey)(
          set.asInstanceOf[Set[(String, AnalysisStore)]].filterNot {
            case (file, _) => file == cacheFile
          } + (cacheFile -> MixedAnalyzingCompiler.staticCachedStore(Paths.get(cacheFile).toFile,
                                                                     !useBinary)),
          Option(Inf)
        )
      case _ => mode.M.pure(())
    }
  }

  lazy val lspCollectAnalyses =
    Def.taskKey[Unit]("language server protocol task to collect analyses locations")
  def lspCollectAnalysesTask = Def.task {
    val cacheFile = compileIncSetup.value.cacheFile.getAbsolutePath
    val useBinary = enableBinaryCompileAnalysis.value
    val s = state.value
    s.log.debug(s"analysis location ${(cacheFile -> useBinary)}")
    import scalacache.modes.sync._
    updateCache(StandardMain.cache)(cacheFile, useBinary)
  }

  private[sbt] def getAnalyses(log: Logger): Future[Seq[Analysis]] = {
    import scalacache.modes.scalaFuture._
    import scala.concurrent.ExecutionContext.Implicits.global
    import java.nio.file.{ Files, Paths }
    StandardMain.cache
      .get(AnalysesKey)
      .collect {
        case Some(a) => a.asInstanceOf[Set[(String, AnalysisStore)]]
      }
      .map { caches =>
        val existingCaches = caches.collect {
          case cache @ (cacheFile, _) if Files.exists(Paths.get(cacheFile)) =>
            cache
        }
        import scala.concurrent.duration.Duration.Inf
        if (existingCaches.size < caches.size)
          StandardMain.cache.put(AnalysesKey)(existingCaches, Option(Inf))
        existingCaches.toSeq.par
          .collect {
            case (_, store) =>
              store.get().toOption.collect {
                case contents =>
                  contents.getAnalysis
              }
          }
          .collect {
            case Some(a: Analysis) => a
          }
          .seq
      }
  }

  def lspDefinition(jsonDefinition: JValue,
                    requestId: String,
                    commandSource: CommandSource,
                    log: Logger)(implicit ec: ExecutionContext): Future[Unit] = Future {
    val LspDefinitionLogHead = "lsp-definition"
    import sjsonnew.support.scalajson.unsafe.CompactPrinter
    log.debug(s"$LspDefinitionLogHead json request: ${CompactPrinter(jsonDefinition)}")
    lazy val analyses = getAnalyses(log)
    val definition = getDefinition(jsonDefinition)
    definition
      .flatMap { definition =>
        val uri = URI.create(definition.textDocument.uri)
        import java.nio.file._
        Files
          .lines(Paths.get(uri))
          .skip(definition.position.line)
          .findFirst
          .toOption
          .flatMap { line =>
            log.debug(s"$LspDefinitionLogHead found line: $line")
            textProcessor
              .identifier(line, definition.position.character.toInt)
          }
      }
      .map { sym =>
        log.debug(s"symbol $sym")
        analyses
          .map { analyses =>
            val locations = analyses.par.flatMap { analysis =>
              val selectPotentials = textProcessor.potentialClsOrTraitOrObj(sym)
              val classes =
                (analysis.apis.allInternalClasses ++ analysis.apis.allExternals).collect {
                  selectPotentials
                }
              log.debug(s"$LspDefinitionLogHead potentials: $classes")
              classes
                .flatMap { className =>
                  analysis.relations.definesClass(className) ++ analysis.relations
                    .libraryDefinesClass(className)
                }
                .flatMap { classFile =>
                  textProcessor.markPosition(classFile, sym).collect {
                    case (file, line, from, to) =>
                      import sbt.internal.langserver.{ Location, Position, Range }
                      Location(file.toURI.toURL.toString,
                               Range(Position(line, from), Position(line, to)))
                  }
                }
            }.seq
            log.debug(s"$LspDefinitionLogHead locations ${locations}")
            import sbt.internal.langserver.codec.JsonProtocol._
            send(commandSource, requestId)(locations.toArray)
          }
          .recover {
            case anyException @ _ =>
              log.warn(s"Problem with processing analyses ${CompactPrinter(jsonDefinition)}")
              import sbt.internal.protocol.JsonRpcResponseError
              import sbt.internal.protocol.codec.JsonRPCProtocol._
              send(commandSource, requestId)(
                JsonRpcResponseError(ErrorCodes.InternalError,
                                     "Problem with processing analyses.",
                                     None))
          }
      }
      .orElse {
        log.info(s"Symbol not found in definition request ${CompactPrinter(jsonDefinition)}")
        import sbt.internal.langserver.Location
        import sbt.internal.langserver.codec.JsonProtocol._
        send(commandSource, requestId)(Array.empty[Location])
        None
      }
  }
}
