// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package org.jetbrains.idea.devkit.dom.impl;

import com.intellij.codeInsight.lookup.LookupElement;
import com.intellij.codeInsight.lookup.LookupElementBuilder;
import com.intellij.codeInsight.lookup.LookupElementPresentation;
import com.intellij.codeInsight.lookup.LookupElementRenderer;
import com.intellij.lang.properties.psi.PropertiesFile;
import com.intellij.lang.properties.psi.Property;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.module.ModuleUtilCore;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.util.Key;
import com.intellij.openapi.util.NullableLazyValue;
import com.intellij.openapi.util.Ref;
import com.intellij.openapi.util.text.StringUtil;
import com.intellij.pom.references.PomService;
import com.intellij.psi.PsiElement;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.search.GlobalSearchScopesCore;
import com.intellij.psi.search.ProjectScope;
import com.intellij.util.ObjectUtils;
import com.intellij.util.Processor;
import com.intellij.util.xml.ConvertContext;
import com.intellij.util.xml.DomTarget;
import com.intellij.util.xml.ElementPresentationManager;
import com.intellij.util.xml.ResolvingConverter;
import org.jetbrains.annotations.*;
import org.jetbrains.idea.devkit.DevKitBundle;
import org.jetbrains.idea.devkit.dom.Action;
import org.jetbrains.idea.devkit.dom.ActionOrGroup;
import org.jetbrains.idea.devkit.dom.Group;
import org.jetbrains.idea.devkit.dom.index.IdeaPluginRegistrationIndex;
import org.jetbrains.idea.devkit.util.DescriptorI18nUtil;

import java.util.*;

import static com.intellij.openapi.util.NullableLazyValue.lazyNullable;

public class ActionOrGroupResolveConverter extends ResolvingConverter<ActionOrGroup> {

  @Override
  public @NotNull Collection<? extends ActionOrGroup> getVariants(@NotNull ConvertContext context) {
    return getVariants(context.getProject(), context.getModule());
  }

  @ApiStatus.Internal
  public @NotNull List<ActionOrGroup> getVariants(@NotNull Project project, @Nullable Module module) {
    final List<ActionOrGroup> variants = new ArrayList<>();
    final Set<String> processedVariants = new HashSet<>();

    processScopes(project, module, scope -> {
      IdeaPluginRegistrationIndex.processAllActionOrGroup(project, scope, actionOrGroup -> {
        if (isRelevant(actionOrGroup) && processedVariants.add(getName(actionOrGroup))) {
          variants.add(actionOrGroup);
        }
        return true;
      });
      return true;
    });
    return variants;
  }

  @Override
  public @Nullable PsiElement getPsiElement(@Nullable ActionOrGroup resolvedValue) {
    if (resolvedValue == null) return null;
    DomTarget target = DomTarget.getTarget(resolvedValue);
    return target == null ? super.getPsiElement(resolvedValue) : PomService.convertToPsi(target);
  }

  @Override
  public @Nullable ActionOrGroup fromString(final @Nullable @NonNls String value, @NotNull ConvertContext context) {
    if (StringUtil.isEmptyOrSpaces(value)) return null;

    final Project project = context.getProject();
    Ref<ActionOrGroup> result = Ref.create();
    processScopes(context.getProject(), context.getModule(), scope -> {
      return IdeaPluginRegistrationIndex.processActionOrGroup(project, value, scope, actionOrGroup -> {
        if (isRelevant(actionOrGroup)) {
          result.set(actionOrGroup);
          return false;
        }
        return true;
      });
    });
    return result.get();
  }

  @Override
  public @Nullable String toString(@Nullable ActionOrGroup actionGroup, @NotNull ConvertContext context) {
    return actionGroup == null ? null : getName(actionGroup);
  }

  @Override
  public String getErrorMessage(@Nullable String s, @NotNull ConvertContext context) {
    return DevKitBundle.message("plugin.xml.convert.action.or.group.cannot.resolve", getResultTypes(), s);
  }

  @Override
  public @Nullable LookupElement createLookupElement(ActionOrGroup actionOrGroup) {
    PsiElement psiElement = getPsiElement(actionOrGroup);
    String name = StringUtil.notNullize(getName(actionOrGroup), DevKitBundle.message("plugin.xml.convert.action.or.group.invalid.name"));
    LookupElementBuilder builder = psiElement == null ? LookupElementBuilder.create(name) :
                                   LookupElementBuilder.create(psiElement, name);
    builder.putUserData(ActionOrGroupLookupRenderer.ACTION_OR_GROUP_KEY, actionOrGroup);
    return builder.withRenderer(ActionOrGroupLookupRenderer.INSTANCE);
  }


  protected boolean isRelevant(ActionOrGroup actionOrGroup) {
    return true;
  }

  protected @Nls String getResultTypes() {
    return DevKitBundle.message("plugin.xml.convert.action.or.group.type.action.or.group");
  }


  public static class OnlyActions extends ActionOrGroupResolveConverter {
    @Override
    protected boolean isRelevant(ActionOrGroup actionOrGroup) {
      return actionOrGroup instanceof Action;
    }

    @Override
    protected String getResultTypes() {
      return DevKitBundle.message("plugin.xml.convert.action.or.group.type.action");
    }
  }

  public static class OnlyGroups extends ActionOrGroupResolveConverter {
    @Override
    protected boolean isRelevant(ActionOrGroup actionOrGroup) {
      return actionOrGroup instanceof Group;
    }

    @Override
    protected String getResultTypes() {
      return DevKitBundle.message("plugin.xml.convert.action.or.group.type.group");
    }
  }


  private static void processScopes(Project project, Module module, final Processor<GlobalSearchScope> processor) {

    if (module == null) {
      final GlobalSearchScope projectScope = GlobalSearchScopesCore.projectProductionScope(project).
        union(ProjectScope.getLibrariesScope(project));
      processor.process(projectScope);
      return;
    }

    ModuleUtilCore.visitMeAndDependentModules(module, module1 -> {
      return processor.process(module1.getModuleRuntimeScope(false));
    });
  }

  private static @Nullable String getName(@NotNull ActionOrGroup actionOrGroup) {
    return actionOrGroup.getId().getStringValue();
  }


  private static class ActionOrGroupLookupRenderer extends LookupElementRenderer<LookupElement> {

    private static final ActionOrGroupLookupRenderer INSTANCE = new ActionOrGroupLookupRenderer();

    private static final Key<ActionOrGroup> ACTION_OR_GROUP_KEY = Key.create("ACTION_OR_GROUP_KEY");

    @Override
    public void renderElement(LookupElement element, LookupElementPresentation presentation) {
      presentation.setItemText(element.getLookupString());

      ActionOrGroup actionOrGroup = element.getUserData(ACTION_OR_GROUP_KEY);
      assert actionOrGroup != null;

      presentation.setItemTextUnderlined(actionOrGroup.getPopup().getValue() == Boolean.TRUE);
      presentation.setIcon(ElementPresentationManager.getIcon(actionOrGroup));

      NullableLazyValue<PropertiesFile> propertiesFile =
        lazyNullable(() -> DescriptorI18nUtil.findBundlePropertiesFile(actionOrGroup));

      final String text = getLocalizedText(actionOrGroup, ActionOrGroup.TextType.TEXT, propertiesFile);
      if (StringUtil.isNotEmpty(text)) {
        String withoutMnemonic = StringUtil.replace(text, "_", "");
        presentation.setTailText(" \"" + withoutMnemonic + "\"", true);
      }

      final String description = getLocalizedText(actionOrGroup, ActionOrGroup.TextType.DESCRIPTION, propertiesFile);
      if (StringUtil.isNotEmpty(description)) {
        presentation.setTypeText(description);
      }
    }

    private static @Nullable String getLocalizedText(ActionOrGroup actionOrGroup,
                                                     ActionOrGroup.TextType text,
                                                     NullableLazyValue<PropertiesFile> propertiesFile) {
      final String plain = text.getDomValue(actionOrGroup).getStringValue();
      if (StringUtil.isNotEmpty(plain)) return plain;

      final PropertiesFile bundleFile = propertiesFile.getValue();
      if (bundleFile == null) return null;

      final Property property = ObjectUtils.tryCast(bundleFile.findPropertyByKey(text.getMessageKey(actionOrGroup)), Property.class);
      return property != null ? property.getValue() : null;
    }
  }
}
