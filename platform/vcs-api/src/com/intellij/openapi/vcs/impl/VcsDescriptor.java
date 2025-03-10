// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.openapi.vcs.impl;

import com.intellij.openapi.application.ReadAction;
import com.intellij.openapi.vcs.AbstractVcs;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.util.containers.ContainerUtil;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.jetbrains.annotations.Unmodifiable;

import java.util.Collections;
import java.util.List;
import java.util.Objects;

public class VcsDescriptor {

  private final String myName;
  private final boolean myAreChildrenValidMappings;
  private final String myDisplayName;
  private final List<String> myAdministrativePatterns;

  public VcsDescriptor(String administrativePattern,
                       String displayName,
                       String name,
                       boolean areChildrenValidMappings) {
    myAdministrativePatterns = parseAdministrativePatterns(administrativePattern);
    myDisplayName = displayName;
    myName = name;
    myAreChildrenValidMappings = areChildrenValidMappings;
  }

  private static @NotNull @Unmodifiable List<String> parseAdministrativePatterns(@Nullable String administrativePattern) {
    if (administrativePattern == null) return Collections.emptyList();
    return ContainerUtil.map(administrativePattern.split(","), it -> it.trim());
  }

  public boolean areChildrenValidMappings() {
    return myAreChildrenValidMappings;
  }

  public boolean probablyUnderVcs(final VirtualFile file) {
    if (myAdministrativePatterns.isEmpty()) return false;
    return ReadAction.compute(() -> matchesVcsDirPattern(file));
  }

  private boolean matchesVcsDirPattern(@Nullable VirtualFile file) {
    if (file == null || !file.isDirectory() || !file.isValid()) return false;
    for (String pattern : myAdministrativePatterns) {
      VirtualFile child = file.findChild(pattern);
      if (child != null) return true;
    }
    return false;
  }

  public boolean hasVcsDirPattern() {
    return !myAdministrativePatterns.isEmpty();
  }

  public boolean matchesVcsDirPattern(@NotNull String dirName) {
    return myAdministrativePatterns.contains(dirName);
  }

  /**
   * @deprecated Prefer {@link AbstractVcs#getDisplayName()}
   */
  @Deprecated(forRemoval = true)
  public String getDisplayName() {
    return myDisplayName == null ? myName : myDisplayName;
  }

  public String getName() {
    return myName;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    VcsDescriptor that = (VcsDescriptor)o;
    return Objects.equals(myName, that.myName);
  }

  @Override
  public int hashCode() {
    return myName != null ? myName.hashCode() : 0;
  }

  @Override
  public String toString() {
    return myName;
  }
}
