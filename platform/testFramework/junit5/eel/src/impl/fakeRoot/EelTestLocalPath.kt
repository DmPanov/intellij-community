// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.platform.testFramework.junit5.eel.impl.fakeRoot

import com.intellij.platform.testFramework.junit5.eel.impl.ownUri.EelTestPath
import java.net.URI
import java.nio.file.FileSystem
import java.nio.file.LinkOption
import java.nio.file.Path
import java.nio.file.WatchEvent
import java.nio.file.WatchKey
import java.nio.file.WatchService

internal class EelTestLocalPath(val fileSystem: EelTestLocalFileSystem, val delegate: EelTestPath) : Path {

  override fun getFileSystem(): FileSystem {
    return fileSystem
  }

  override fun isAbsolute(): Boolean {
    return delegate.isAbsolute
  }

  override fun getRoot(): EelTestLocalPath {
    return fileSystem.root
  }

  override fun getFileName(): Path? {
    return EelTestLocalPath(fileSystem, delegate.fileName)
  }

  override fun getParent(): Path? {
    val parent = delegate.parent ?: return null
    return EelTestLocalPath(fileSystem, parent)
  }

  override fun getNameCount(): Int {
    if (delegate == fileSystem.root.delegate) {
      return 0
    }
    return delegate.nameCount - root.delegate.nameCount
  }

  override fun getName(index: Int): Path {
    return EelTestLocalPath(fileSystem, delegate.getName(index))
  }

  override fun subpath(beginIndex: Int, endIndex: Int): Path {
    return EelTestLocalPath(fileSystem, delegate.subpath(beginIndex, endIndex))
  }

  override fun startsWith(other: Path): Boolean {
    require(other is EelTestLocalPath)
    return delegate.startsWith(other.delegate)
  }

  override fun endsWith(other: Path): Boolean {
    require(other is EelTestLocalPath)
    return delegate.endsWith(other.delegate)
  }

  override fun normalize(): Path {
    return EelTestLocalPath(fileSystem, delegate.normalize())
  }

  override fun resolve(other: Path): Path {
    require(other is EelTestLocalPath)
    return EelTestLocalPath(fileSystem, delegate.resolve(other.delegate))
  }

  override fun relativize(other: Path): Path {
    require(other is EelTestLocalPath)
    return EelTestLocalPath(fileSystem, delegate.relativize(other.delegate))
  }

  override fun toUri(): URI {
    TODO()
  }

  override fun toAbsolutePath(): Path {
    return EelTestLocalPath(fileSystem, delegate.toAbsolutePath())
  }

  override fun toRealPath(vararg options: LinkOption): Path {
    return EelTestLocalPath(fileSystem, delegate.toRealPath(*options))
  }

  override fun register(watcher: WatchService, events: Array<out WatchEvent.Kind<*>>?, vararg modifiers: WatchEvent.Modifier?): WatchKey {
    return delegate.register(watcher, events, *modifiers)
  }

  override fun compareTo(other: Path): Int {
    require(other is EelTestLocalPath)
    return delegate.compareTo(other.delegate)
  }

  override fun equals(other: Any?): Boolean {
    return other is EelTestLocalPath && other.fileSystem == fileSystem && other.delegate == delegate
  }

  override fun toString(): String {
    return if (isAbsolute) {
      if (delegate.nameCount == 0) {
        return fileSystem.fakeLocalRoot
      }
      else {
        fileSystem.fakeLocalRoot + fileSystem.separator + delegate.toString().substring(fileSystem.rootDirectory.toString().length + 1)
      }
    }
    else {
      delegate.toString()
    }
  }

  override fun hashCode(): Int {
    var result = fileSystem.hashCode()
    result = 31 * result + delegate.hashCode()
    return result
  }
}