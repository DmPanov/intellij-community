// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
@file:Suppress("ReplacePutWithAssignment")
package org.jetbrains.intellij.build.impl

import com.intellij.openapi.util.SystemInfoRt
import com.jetbrains.signatureverifier.ILogger
import com.jetbrains.signatureverifier.InvalidDataException
import com.jetbrains.signatureverifier.PeFile
import com.jetbrains.signatureverifier.SignatureData
import com.jetbrains.signatureverifier.crypt.SignatureVerificationParams
import com.jetbrains.signatureverifier.crypt.SignedMessage
import com.jetbrains.signatureverifier.crypt.SignedMessageVerifier
import com.jetbrains.signatureverifier.crypt.VerifySignatureStatus
import com.jetbrains.signatureverifier.macho.MachoArch
import com.jetbrains.util.Rewind
import com.jetbrains.util.filetype.FileType
import com.jetbrains.util.filetype.FileTypeDetector.DetectFileType
import io.opentelemetry.api.common.AttributeKey
import io.opentelemetry.api.trace.Span
import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.persistentMapOf
import kotlinx.coroutines.CoroutineName
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import org.jetbrains.intellij.build.BuildContext
import org.jetbrains.intellij.build.BuildOptions
import org.jetbrains.intellij.build.io.*
import org.jetbrains.intellij.build.BuildPaths
import org.jetbrains.intellij.build.OsFamily
import org.jetbrains.intellij.build.telemetry.TraceManager.spanBuilder
import org.jetbrains.intellij.build.telemetry.use
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.channels.SeekableByteChannel
import java.nio.file.*
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.attribute.FileTime
import java.util.concurrent.TimeUnit
import kotlin.io.path.appendText
import kotlin.io.path.exists
import kotlin.io.path.extension
import kotlin.io.path.name
import kotlin.io.path.readLines
import kotlin.io.path.relativeTo

internal fun isMacLibrary(name: String): Boolean {
  return name.endsWith(".jnilib") ||
         name.endsWith(".dylib") ||
         name.endsWith(".so") ||
         name.endsWith(".tbd")
}

private fun isWindowsBinary(name: String): Boolean {
  return name.endsWith(".dll") || name.endsWith(".exe")
}

private fun isArchive(name: String): Boolean {
  return name.endsWith(".jar") || name.endsWith(".zip")
}

/**
 * See [BuildOptions.WIN_SIGN_STEP] implementation in [WindowsDistributionBuilder]
 */
private fun BuildContext.isBuildTimeSigned(relativePath: String): Boolean {
  return relativePath.startsWith("bin/") || windowsDistributionCustomizer
    ?.getBinariesToSign(this)
    ?.contains(relativePath) == true
}

internal suspend fun recursivelyVerifyWindowsSignatures(context: BuildContext) {
  coroutineScope {
    (sequenceOf(context.paths.distAllDir) + SUPPORTED_DISTRIBUTIONS.filter { it.os == OsFamily.WINDOWS }.flatMap { (os, arch) ->
      val runtimeDist = context.bundledRuntime.extract(os = os, arch = arch)
      sequence {
        yield(runtimeDist)
        if (context.shouldBuildDistributionForOS(os, arch)) {
          yield(getOsAndArchSpecificDistDirectory(os, arch, context))
        }
      }
    }).filter { it.exists() }.forEach {
      launch(CoroutineName("verifying Windows binaries in $it")) {
        recursivelyVerifyWindowsSignatures(it, context)
      }
    }
  }
}

private fun CoroutineScope.recursivelyVerifyWindowsSignatures(root: Path, context: BuildContext) {
  Files.walkFileTree(root, object : SimpleFileVisitor<Path>() {
    override fun visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult {
      val name = file.name
      if (isArchive(name)) {
        launch(CoroutineName("verifying Windows binaries in ${file.relativeTo(root)}")) {
          unpackZipAndVerifyWindowsSignatures(file, context)
        }
      }
      else if (isWindowsBinary(name) && !context.isBuildTimeSigned(file.relativeTo(root).toString())) {
        launch(CoroutineName("verifying Windows binary $name")) {
          Files.newByteChannel(file).use {
            if (isWindowsBinary(it) && !isWindowsSigned(it, binaryId = "$file")) {
              context.messages.reportBuildProblem("Binary $file is not signed", identity = "$file")
            }
          }
        }
      }
      return FileVisitResult.CONTINUE
    }
  })
}

private suspend fun unpackZipAndVerifyWindowsSignatures(zip: Path, context: BuildContext) {
  suspendAwareReadZipFile(zip) { name, dataSupplier ->
    if (isWindowsBinary(name)) {
      val data = with(dataSupplier()) {
        /**
         * See [detectFileType]
         */
        if (position() > 0) slice() else this
      }
      ByteBufferChannel(data).use {
        if (isWindowsBinary(it) && !isWindowsSigned(it, name)) {
          context.messages.reportBuildProblem("Binary $zip!$name is not signed", identity = "$zip!$name")
        }
      }
    }
  }
}

internal object BinariesAutoSignList {
  private val listUpdateMutex = Mutex()
  private val list: Path = BuildPaths.COMMUNITY_ROOT.communityRoot.resolve("../build/binaries-autosign.txt")

  suspend fun register(binaryId: String) {
    listUpdateMutex.withLock {
      if (!list.readLines().contains(binaryId)) {
        list.appendText("$binaryId\n")
        println("$binaryId is added to ${list.name}")
      }
    }
  }
}

internal fun CoroutineScope.recursivelySignMacBinaries(
  root: Path,
  context: BuildContext,
  executableFileMatchers: Collection<PathMatcher> = emptyList(),
) {
  val archives = mutableListOf<Path>()
  val binaries = mutableListOf<Path>()

  Files.walkFileTree(root, object : SimpleFileVisitor<Path>() {
    override fun visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult {
      val relativePath = root.relativize(file)
      val name = file.name
      if (isArchive(name)) {
        archives.add(file)
      }
      else if (isMacLibrary(name) ||
               executableFileMatchers.any { it.matches(relativePath) } ||
               (SystemInfoRt.isUnix && Files.isExecutable(file))) {
        binaries.add(file)
      }
      return FileVisitResult.CONTINUE
    }
  })

  launch(CoroutineName("signing macOS binaries")) {
    signMacBinaries(binaries.filter { binary ->
      Files.newByteChannel(binary).use {
        isMacBinary(it) &&
        !isMacBinarySigned(it, binaryId = "$binary")
      }
    }, context)
  }

  for (file in archives) {
    launch(CoroutineName("signing macOS binaries in ${file.relativeTo(root)}")) {
      signAndRepackZipIfMacSignaturesAreMissing(file, context)
    }
  }
}

private suspend fun signAndRepackZipIfMacSignaturesAreMissing(zip: Path, context: BuildContext) {
  val filesToBeSigned = LinkedHashMap<String, Path>()
  suspendAwareReadZipFile(zip) { name, dataSupplier ->
    if (!isMacLibrary(name)) {
      return@suspendAwareReadZipFile
    }

    val data = dataSupplier()
    ByteBufferChannel(data).use { byteChannel ->
      data.mark()
      if (isMacBinary(byteChannel)) {
        data.reset()
        if (!isMacBinarySigned(byteChannel, name)) {
          data.reset()
          val fileToBeSigned = Files.createTempFile(context.paths.tempDir, name.replace('/', '-').takeLast(128), "")
          writeToFile(fileToBeSigned, data)

          filesToBeSigned.put(name, fileToBeSigned)
        }
      }
    }
  }

  if (filesToBeSigned.isEmpty()) {
    return
  }

  signMacBinaries(files = filesToBeSigned.values.toList(), context = context, checkPermissions = false)

  copyZipReplacing(origin = zip, entries = filesToBeSigned, context = context)
  for (file in filesToBeSigned.values) {
    Files.deleteIfExists(file)
  }
}

private suspend fun copyZipReplacing(origin: Path, entries: Map<String, Path>, context: BuildContext) {
  spanBuilder("replacing unsigned entries in zip")
    .setAttribute("zip", origin.toString())
    .setAttribute(AttributeKey.stringArrayKey("unsigned"), entries.keys.toList())
    .use {
      val packageIndexBuilder = PackageIndexBuilder(AddDirEntriesMode.NONE)
      writeZipUsingTempFile(file = origin, packageIndexBuilder) { zipWriter ->
        readZipFile(origin) { name, dataSupplier ->
          packageIndexBuilder.addFile(name)
          if (entries.containsKey(name)) {
            zipWriter.file(name, entries.getValue(name))
          }
          else {
            zipWriter.uncompressedData(name, dataSupplier())
          }
          ZipEntryProcessorResult.CONTINUE
        }
      }
      Files.setLastModifiedTime(origin, FileTime.from(context.options.buildDateInSeconds, TimeUnit.SECONDS))
    }
}

internal fun macSigningOptions(contentType: String, context: BuildContext): PersistentMap<String, String> {
  val certificateID = context.proprietaryBuildTools.macOsCodesignIdentity?.value
  check(certificateID != null || context.isStepSkipped(BuildOptions.MAC_SIGN_STEP)) {
    "Missing certificate ID"
  }
  val entitlements = context.paths.communityHomeDir.resolve("platform/build-scripts/tools/mac/scripts/entitlements.xml")
  check(entitlements.exists()) {
    "Missing $entitlements file"
  }
  return persistentMapOf(
    "mac_codesign_options" to "runtime",
    "mac_codesign_identity" to "$certificateID",
    "mac_codesign_entitlements" to "$entitlements",
    "mac_codesign_force" to "true", // true if omitted
    "contentType" to contentType
  )
}

internal suspend fun signMacBinaries(
  files: List<Path>,
  context: BuildContext,
  checkPermissions: Boolean = true,
  additionalOptions: Map<String, String> = emptyMap(),
) {
  if (files.isEmpty() || !context.isMacCodeSignEnabled) {
    return
  }

  check(files.none { it.extension == "sit" })
  val permissions = if (checkPermissions && SystemInfoRt.isUnix) {
    files.associateWith {
      HashSet(Files.getPosixFilePermissions(it))
    }
  }
  else {
    emptyMap()
  }

  val span = spanBuilder("sign binaries for macOS distribution")
  span.setAttribute("contentType", "application/x-mac-app-bin")
  span.setAttribute(AttributeKey.stringArrayKey("files"), files.map { it.name })
  val options = macSigningOptions(contentType = "application/x-mac-app-bin", context = context).putAll(m = additionalOptions)
  span.use {
    for (file in files) {
      BinariesAutoSignList.register(
        binaryId = when {
          file.startsWith(context.paths.tempDir) -> context.paths.tempDir
          file.startsWith(context.paths.distAllDir) -> context.paths.distAllDir
          file.startsWith(context.paths.buildOutputDir) -> context.paths.buildOutputDir
          else -> error("Unexpected binary location: $file")
        }.relativize(file).toString()
      )
    }
    context.signFiles(files = files, options = options)
    if (!permissions.isEmpty()) {
      // SRE-1223 workaround
      files.forEach {
        Files.setPosixFilePermissions(it, permissions.getValue(it))
      }
    }

    val missingSignature = files.filterNot { isMacBinarySigned(it) }
    check(missingSignature.isEmpty()) {
      "Missing signature for:\n" + missingSignature.joinToString(separator = "\n\t")
    }
  }
}

internal suspend fun signData(data: ByteBuffer, fileName: String, context: BuildContext, options: PersistentMap<String, String>): Path {
  val file = Files.createTempFile(context.paths.tempDir, "signData", fileName)
  writeToFile(file, data)
  context.signFiles(files = listOf(file), options = options)
  return file
}

private fun writeToFile(file: Path?, data: ByteBuffer) {
  FileChannel.open(file, WRITE_OPEN_OPTION).use { fileChannel ->
    writeToFileChannelFully(channel = fileChannel, data = data)
  }
}

internal suspend fun isMacBinarySigned(path: Path): Boolean {
  return withContext(Dispatchers.IO) {
    Files.newByteChannel(path).use {
      isMacBinarySigned(byteChannel = it, binaryId = path.toString())
    }
  }
}

/**
 * @param byteChannel should be closed by a caller
 */
internal suspend fun isMacBinary(byteChannel: SeekableByteChannel): Boolean {
  return byteChannel.detectFileType() == FileType.MachO
}

internal suspend fun isWindowsBinarySigned(path: Path): Boolean {
  return withContext(Dispatchers.IO) {
    Files.newByteChannel(path).use {
      isWindowsSigned(byteChannel = it, binaryId = "$path")
    }
  }
}

/**
 * @param byteChannel should be closed by a caller
 */
private suspend fun isWindowsBinary(byteChannel: SeekableByteChannel): Boolean {
  return byteChannel.detectFileType() == FileType.Pe
}

/**
 * See [withRewind]
 */
internal suspend fun SeekableByteChannel.detectFileType(): FileType {
  return withRewind {
    DetectFileType().first
  }
}

/**
 * Assumes [isMacBinary].
 * See [withRewind].
 */
internal suspend fun isMacBinarySigned(byteChannel: SeekableByteChannel, binaryId: String): Boolean {
  val verificationParams = SignatureVerificationParams(
    signRootCertStore = null,
    timestampRootCertStore = null,
    buildChain = false,
    withRevocationCheck = false
  )
  return byteChannel.withRewind {
    val binaries = MachoArch(byteChannel).Extract()
    binaries.all { binary ->
      isSigned(verificationParams, binaryId) {
        binary.GetSignatureData()
      }
    }
  }
}

/**
 * See [withRewind]
 */
internal suspend fun isWindowsSigned(byteChannel: SeekableByteChannel, binaryId: String): Boolean {
  val verificationParams = SignatureVerificationParams(
    signRootCertStore = null,
    timestampRootCertStore = null,
    buildChain = false,
    withRevocationCheck = false
  )
  return byteChannel.withRewind {
    isSigned(verificationParams, binaryId = binaryId) {
      PeFile(byteChannel).GetSignatureData()
    }
  }
}

/**
 * `format-ripper` library rewinds [SeekableByteChannel.position] to 0 with [Rewind], so this method fails if [SeekableByteChannel.position] > 0.
 * Please use [ByteBuffer.slice] as a source for [SeekableByteChannel] instead.
 */
private suspend fun <T> SeekableByteChannel.withRewind(action: suspend SeekableByteChannel.() -> T): T {
  check(position() == 0L) {
    "SeekableByteChannel#position = ${position()} but 0 is required. " +
    "Please use ByteBuffer#slice as a source for SeekableByteChannel instead."
  }
  return try {
    action()
  }
  finally {
    Rewind()
  }
}

private suspend fun isSigned(
  verificationParams: SignatureVerificationParams,
  binaryId: String,
  signatureDataSupplier: () -> SignatureData,
): Boolean {
  val signatureData = try {
    signatureDataSupplier()
  }
  catch (_: InvalidDataException) {
    return false
  }

  if (signatureData.IsEmpty) {
    return false
  }

  val signedMessage = try {
    SignedMessage.CreateInstance(signatureData)
  }
  catch (_: Exception) {
    // assuming Signature=adhoc
    return false
  }

  val result = try {
    val signedMessageVerifier = SignedMessageVerifier(SignatureVerificationLog(binaryId))
    signedMessageVerifier.VerifySignatureAsync(signedMessage, verificationParams)
  }
  catch (e: Exception) {
    throw Exception("Failed to verify $binaryId", e)
  }
  return result.Status == VerifySignatureStatus.Valid
}

private class SignatureVerificationLog(val binaryId: String) : ILogger {
  private val span: Span = Span.current()

  fun addEvent(str: String, category: String) {
    span.addEvent(str)
      .setAttribute("binary", binaryId)
      .setAttribute("category", category)
  }

  override fun Info(str: String) = addEvent(str, "INFO")
  override fun Warning(str: String) = addEvent(str, "WARN")
  override fun Error(str: String) = addEvent(str, "ERROR")
  override fun Trace(str: String) {}
}
