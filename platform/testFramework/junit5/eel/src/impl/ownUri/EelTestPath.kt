// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.platform.testFramework.junit5.eel.impl.ownUri

import java.net.URI
import java.nio.file.FileSystem
import java.nio.file.LinkOption
import java.nio.file.Path
import java.nio.file.WatchEvent
import java.nio.file.WatchKey
import java.nio.file.WatchService

internal class EelTestPath(val fileSystem: EelTestFileSystem, val delegate: Path) : Path {

  init {
    require(delegate !is EelTestPath)
  }

  override fun getFileSystem(): FileSystem {
    return fileSystem
  }

  override fun isAbsolute(): Boolean {
    return delegate.isAbsolute
  }

  override fun getRoot(): EelTestPath {
    return fileSystem.root
  }

  override fun getFileName(): EelTestPath {
    return EelTestPath(fileSystem, delegate.fileName)
  }

  override fun getParent(): EelTestPath? {
    val parent = delegate.parent ?: return null
    return EelTestPath(fileSystem, parent)
  }

  override fun getNameCount(): Int {
    if (delegate == fileSystem.root.delegate) {
      return 0
    }
    return delegate.nameCount - root.delegate.nameCount
  }

  override fun getName(index: Int): EelTestPath {
    return EelTestPath(fileSystem, delegate.getName(index + root.delegate.nameCount))
  }

  override fun subpath(beginIndex: Int, endIndex: Int): EelTestPath {
    return EelTestPath(fileSystem, delegate.subpath(beginIndex + root.delegate.nameCount, endIndex + root.delegate.nameCount))
  }

  override fun startsWith(other: Path): Boolean {
    require(other is EelTestPath)
    return delegate.startsWith(other.delegate)
  }

  override fun endsWith(other: Path): Boolean {
    require(other is EelTestPath)
    return delegate.endsWith(other.delegate)
  }

  override fun normalize(): EelTestPath {
    return EelTestPath(fileSystem, delegate.normalize())
  }

  override fun resolve(other: Path): EelTestPath {
    require(other is EelTestPath)
    return EelTestPath(fileSystem, delegate.resolve(other.delegate))
  }

  override fun relativize(other: Path): EelTestPath {
    require(other is EelTestPath)
    return EelTestPath(fileSystem, delegate.relativize(other.delegate))
  }

  override fun toUri(): URI {
    TODO()
  }

  override fun toAbsolutePath(): EelTestPath {
    return EelTestPath(fileSystem, delegate.toAbsolutePath())
  }

  override fun toRealPath(vararg options: LinkOption): EelTestPath {
    return EelTestPath(fileSystem, delegate.toRealPath(*options))
  }

  override fun register(watcher: WatchService, events: Array<out WatchEvent.Kind<*>>?, vararg modifiers: WatchEvent.Modifier?): WatchKey {
    return delegate.register(watcher, events, *modifiers)
  }

  override fun resolve(other: String): EelTestPath {
    return super.resolve(other) as EelTestPath
  }


  override fun compareTo(other: Path): Int {
    require(other is EelTestPath)
    return delegate.compareTo(other.delegate)
  }

  override fun equals(other: Any?): Boolean {
    return other is EelTestPath && other.fileSystem == fileSystem && other.delegate == delegate
  }

  override fun toString(): String {
    return delegate.toString()
  }

  override fun hashCode(): Int {
    var result = fileSystem.hashCode()
    result = 31 * result + delegate.hashCode()
    return result
  }
}