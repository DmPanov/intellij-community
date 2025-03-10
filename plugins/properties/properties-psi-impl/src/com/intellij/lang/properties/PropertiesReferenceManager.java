// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.lang.properties;

import com.intellij.lang.properties.psi.PropertiesFile;
import com.intellij.lang.properties.xml.XmlPropertiesIndex;
import com.intellij.openapi.components.Service;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.project.DumbService;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.PsiFile;
import com.intellij.psi.PsiManager;
import com.intellij.psi.search.FileTypeIndex;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.util.CachedValueProvider;
import com.intellij.psi.util.CachedValuesManager;
import com.intellij.psi.util.PsiModificationTracker;
import com.intellij.util.containers.ConcurrentFactoryMap;
import com.intellij.util.indexing.FileBasedIndex;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.ConcurrentMap;

@Service(Service.Level.PROJECT)
public final class PropertiesReferenceManager {
  private final PsiManager myPsiManager;
  private final DumbService myDumbService;

  public static PropertiesReferenceManager getInstance(@NotNull Project project) {
    return project.getService(PropertiesReferenceManager.class);
  }

  public PropertiesReferenceManager(@NotNull Project project) {
    myPsiManager = PsiManager.getInstance(project);
    myDumbService = DumbService.getInstance(project);
  }

  public @NotNull List<PropertiesFile> findPropertiesFiles(@NotNull Module module, @NotNull String bundleName) {
    ConcurrentMap<String, List<PropertiesFile>> map =
      CachedValuesManager.getManager(module.getProject()).getCachedValue(module, () -> {
        ConcurrentMap<String, List<PropertiesFile>> factoryMap = ConcurrentFactoryMap.createMap(
          bundleName1 -> findPropertiesFiles(GlobalSearchScope.moduleRuntimeScope(module, true), bundleName1,
                                             BundleNameEvaluator.DEFAULT));
        return CachedValueProvider.Result.create(factoryMap, PsiModificationTracker.MODIFICATION_COUNT);
      });
    return map.get(bundleName);
  }

  public @NotNull List<PropertiesFile> findPropertiesFiles(@NotNull GlobalSearchScope searchScope,
                                                           @NotNull String bundleName,
                                                           @NotNull BundleNameEvaluator bundleNameEvaluator) {


    final ArrayList<PropertiesFile> result = new ArrayList<>();
    processPropertiesFiles(searchScope, (baseName, propertiesFile) -> {
      if (baseName.equals(bundleName)) {
        result.add(propertiesFile);
      }
      return true;
    }, bundleNameEvaluator);
    return result;
  }

  public @Nullable PropertiesFile findPropertiesFile(@NotNull Module module,
                                                     @NotNull String bundleName,
                                                     @Nullable Locale locale) {
    List<PropertiesFile> propFiles = findPropertiesFiles(module, bundleName);
    if (locale != null) {
      for(PropertiesFile propFile: propFiles) {
        if (propFile.getLocale().equals(locale)) {
          return propFile;
        }
      }
    }

    // fallback to default locale
    for(PropertiesFile propFile: propFiles) {
      if (propFile.getLocale().getLanguage().length() == 0 || propFile.getLocale().equals(Locale.getDefault())) {
        return propFile;
      }
    }

    // fallback to any file
    if (!propFiles.isEmpty()) {
      return propFiles.get(0);
    }

    return null;
  }

  public boolean processAllPropertiesFiles(final @NotNull PropertiesFileProcessor processor) {
    return processPropertiesFiles(GlobalSearchScope.allScope(myPsiManager.getProject()), processor, BundleNameEvaluator.DEFAULT);
  }

  public boolean processPropertiesFiles(final @NotNull GlobalSearchScope searchScope,
                                        final @NotNull PropertiesFileProcessor processor,
                                        final @NotNull BundleNameEvaluator evaluator) {
    for(VirtualFile file:FileTypeIndex.getFiles(PropertiesFileType.INSTANCE, searchScope)) {
      if (!processFile(file, evaluator, processor)) return false;
    }
    if (!myDumbService.isDumb()) {
      for(VirtualFile file:FileBasedIndex.getInstance().getContainingFiles(XmlPropertiesIndex.NAME, XmlPropertiesIndex.MARKER_KEY, searchScope)) {
        if (!processFile(file, evaluator, processor)) return false;
      }
    }

    return true;
  }

  private boolean processFile(@NotNull VirtualFile file, @NotNull BundleNameEvaluator evaluator, @NotNull PropertiesFileProcessor processor) {
    final PsiFile psiFile = myPsiManager.findFile(file);
    PropertiesFile propertiesFile = PropertiesImplUtil.getPropertiesFile(psiFile);
    if (propertiesFile != null) {
      final String qName = evaluator.evaluateBundleName(psiFile);
      if (qName != null) {
        if (!processor.process(qName, propertiesFile)) return false;
      }
    }
    return true;
  }
}
