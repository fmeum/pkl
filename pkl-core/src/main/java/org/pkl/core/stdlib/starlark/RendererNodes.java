/*
 * Copyright © 2024-2025 Apple Inc. and the Pkl project authors. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.pkl.core.stdlib.starlark;

import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.dsl.Specialization;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import org.pkl.core.runtime.Identifier;
import org.pkl.core.runtime.VmBytes;
import org.pkl.core.runtime.VmDataSize;
import org.pkl.core.runtime.VmDuration;
import org.pkl.core.runtime.VmDynamic;
import org.pkl.core.runtime.VmIntSeq;
import org.pkl.core.runtime.VmList;
import org.pkl.core.runtime.VmListing;
import org.pkl.core.runtime.VmMap;
import org.pkl.core.runtime.VmMapping;
import org.pkl.core.runtime.VmNull;
import org.pkl.core.runtime.VmPair;
import org.pkl.core.runtime.VmRegex;
import org.pkl.core.runtime.VmSet;
import org.pkl.core.runtime.VmTyped;
import org.pkl.core.runtime.VmUtils;
import org.pkl.core.stdlib.AbstractStringRenderer;
import org.pkl.core.stdlib.ExternalMethod1Node;
import org.pkl.core.stdlib.PklConverter;
import org.pkl.core.util.ArrayCharEscaper;
import org.pkl.core.util.IoUtils;
import org.pkl.core.util.Nullable;

public final class RendererNodes {

  private static Renderer createRenderer(VmTyped self, StringBuilder builder) {
    var indent = (String) VmNull.unwrap(VmUtils.readMember(self, Identifier.INDENT));
    if (indent == null) {
      indent = "";
    }
    var omitNullProperties = (boolean) VmUtils.readMember(self, Identifier.OMIT_NULL_PROPERTIES);
    return new Renderer(builder, indent, omitNullProperties, PklConverter.fromRenderer(self));
  }

  public abstract static class renderDocument extends ExternalMethod1Node {

    @Specialization
    @TruffleBoundary
    protected String eval(VmTyped self, Object value) {
      var builder = new StringBuilder();
      createRenderer(self, builder).renderDocument(value);
      return builder.toString();
    }
  }

  public abstract static class renderValue extends ExternalMethod1Node {

    @Specialization
    @TruffleBoundary
    protected String eval(VmTyped self, Object value) {
      var builder = new StringBuilder();
      createRenderer(self, builder).renderValue(value);
      return builder.toString();
    }
  }

  private static final class Renderer extends AbstractStringRenderer {

    // Starlark string escaper for double-quoted strings.
    private static final ArrayCharEscaper STRING_ESCAPER;

    static {
      var builder = ArrayCharEscaper.builder();
      // Control characters
      for (char ch = 0; ch < 0x20; ch++) {
        builder.withEscape(ch, IoUtils.toUnicodeEscape(ch));
      }
      STRING_ESCAPER =
        builder
          .withEscape('\\', "\\\\")
          .withEscape('"', "\\\"")
          .withEscape('\n', "\\n")
          .withEscape('\r', "\\r")
          .withEscape('\t', "\\t")
          .build();
    }

    /**
     * The top-level document value (module or object whose properties become top-level Starlark
     * statements). Set to non-null only during {@link #visitDocument}.
     */
    private @Nullable Object documentModule = null;

    /**
     * Tracks nesting depth for typed and dynamic objects. Incremented in startTyped/startDynamic,
     * decremented in endTyped/endDynamic.
     *
     * <ul>
     *   <li>0 = before entering the document-level object
     *   <li>1 = inside the document-level object (module properties at this depth)
     *   <li>2+ = nested objects
     * </ul>
     */
    private int objectDepth = 0;

    /**
     * When set, the next startTyped call will render a rule call (top-level class instantiation)
     * with this as the injected {@code name} argument.
     */
    private @Nullable String pendingRuleName = null;

    /**
     * The object depth at which the current rule call started, or -1 if not inside a rule call.
     * Used to skip the class's own {@code name} property (already injected) and to write the rule
     * call's closing paren with a trailing newline.
     */
    private int ruleCallStartDepth = -1;

    /**
     * Whether the rule call header (with injected {@code name}) has been written. Used to ensure a
     * trailing comma is always added between the injected name and subsequent properties, even when
     * the class's own {@code name} property is the first property encountered.
     */
    private boolean ruleCallHeaderWritten = false;

    private final boolean renderInline;

    /**
     * Maps Bazel load labels to the set of symbols to load from each label. Populated during
     * rendering when classes annotated with {@code @pkl.starlark#LoadLabel} are encountered.
     * Non-null only during {@link #visitDocument}.
     */
    private @Nullable LinkedHashMap<String, LinkedHashSet<String>> loadLabels = null;

    private Renderer(
      StringBuilder builder, String indent, boolean omitNullProperties, PklConverter converter) {
      super("Starlark", builder, indent, converter, omitNullProperties, omitNullProperties);
      renderInline = indent.isEmpty();
    }

    /**
     * Sorts properties of nested objects (not the top-level document module) alphabetically by
     * name to produce deterministic, canonical Starlark output.
     */
    @Override
    protected @Nullable Comparator<Object> memberSortComparator(Object value) {
      if (value == documentModule) return null;
      return Comparator.comparing(Object::toString);
    }

    @Override
    protected void visitDocument(Object value) {
      if (value instanceof VmTyped || value instanceof VmDynamic) {
        documentModule = value;
        loadLabels = new LinkedHashMap<>();
      }
      var startPos = builder.length();
      visit(value);
      if (loadLabels != null && !loadLabels.isEmpty()) {
        var header = new StringBuilder();
        for (var entry : loadLabels.entrySet()) {
          header.append("load(\"").append(entry.getKey()).append('"');
          for (var symbol : entry.getValue()) {
            header.append(", \"").append(symbol).append('"');
          }
          header.append(')').append(LINE_BREAK);
        }
        header.append(LINE_BREAK);
        builder.insert(startPos, header);
      }
      loadLabels = null;
      documentModule = null;
    }

    @Override
    protected void visitTopLevelValue(Object value) {
      visit(value);
    }

    @Override
    protected void visitRenderDirective(VmTyped value) {
      builder.append(VmUtils.readTextProperty(value));
    }

    // --- Primitives ---

    @Override
    public void visitNull(VmNull value) {
      builder.append("None");
    }

    @Override
    public void visitBoolean(Boolean value) {
      builder.append(value ? "True" : "False");
    }

    @Override
    public void visitInt(Long value) {
      builder.append(value);
    }

    @Override
    public void visitFloat(Double value) {
      builder.append(value);
    }

    @Override
    public void visitString(String value) {
      builder.append('"').append(STRING_ESCAPER.escape(value)).append('"');
    }

    @Override
    public void visitDuration(VmDuration value) {
      cannotRenderTypeAddConverter(value);
    }

    @Override
    public void visitDataSize(VmDataSize value) {
      cannotRenderTypeAddConverter(value);
    }

    @Override
    public void visitBytes(VmBytes value) {
      cannotRenderTypeAddConverter(value);
    }

    @Override
    public void visitIntSeq(VmIntSeq value) {
      cannotRenderTypeAddConverter(value);
    }

    @Override
    public void visitPair(VmPair value) {
      cannotRenderTypeAddConverter(value);
    }

    @Override
    public void visitRegex(VmRegex value) {
      cannotRenderTypeAddConverter(value);
    }

    // --- List / Set / Listing → [...] ---

    @Override
    protected void startList(VmList value) {
      startArray();
    }

    @Override
    protected void startSet(VmSet value) {
      builder.append("set(");
      startArray();
    }

    @Override
    protected void startListing(VmListing value) {
      startArray();
    }

    @Override
    protected void endList(VmList value) {
      endArray(value.isEmpty());
    }

    @Override
    protected void endSet(VmSet value) {
      endArray(value.isEmpty());
      builder.append(')');
    }

    @Override
    protected void endListing(VmListing value, boolean isEmpty) {
      endArray(isEmpty);
    }

    private void startArray() {
      builder.append('[');
      increaseIndent();
    }

    private void endArray(boolean isEmpty) {
      decreaseIndent();
      if (!isEmpty && !renderInline) {
        builder.append(',').append(LINE_BREAK).append(currIndent);
      }
      builder.append(']');
    }

    @Override
    protected void visitElement(long index, Object value, boolean isFirst) {
      if (!isFirst) {
        builder.append(',');
      }
      if (!isFirst || !renderInline) {
        builder.append(LINE_BREAK).append(currIndent);
      }
      visit(value);
    }

    // --- Map / Mapping → {...} ---

    @Override
    protected void startMap(VmMap value) {
      startDict();
    }

    @Override
    protected void startMapping(VmMapping value) {
      startDict();
    }

    @Override
    protected void endMap(VmMap value) {
      endDict(value.isEmpty());
    }

    @Override
    protected void endMapping(VmMapping value, boolean isEmpty) {
      endDict(isEmpty);
    }

    private void startDict() {
      builder.append('{');
      increaseIndent();
    }

    private void endDict(boolean isEmpty) {
      decreaseIndent();
      if (!isEmpty && !renderInline) {
        builder.append(',').append(LINE_BREAK).append(currIndent);
      }
      builder.append('}');
    }

    @Override
    protected void visitEntryKey(Object key, boolean isFirst) {
      if (!isFirst) {
        builder.append(',');
      }
      if (!renderInline) {
        builder.append(LINE_BREAK).append(currIndent);
      } else if (!isFirst) {
        builder.append(' ');
      }
      if (key instanceof String s) {
        visitString(s);
      } else if (isRenderDirective(key)) {
        visitRenderDirective((VmTyped) key);
      } else {
        cannotRenderNonStringKey(key);
      }
      builder.append(": ");
    }

    @Override
    protected void visitEntryValue(Object value) {
      visit(value);
    }

    // --- Dynamic → struct(...) or [...] ---

    @Override
    protected void startDynamic(VmDynamic value) {
      objectDepth++;
      if (value == documentModule) {
        // Top-level module as dynamic — no rendering needed.
        return;
      }
      if (value.hasElements()) {
        startArray();
      } else {
        builder.append("struct(");
        increaseIndent();
      }
    }

    @Override
    protected void endDynamic(VmDynamic value, boolean isEmpty) {
      if (value == documentModule) {
        objectDepth--;
        return;
      }
      if (value.hasElements()) {
        endArray(isEmpty);
      } else {
        endFunctionCall(!isEmpty);
      }
      objectDepth--;
    }

    // --- Typed → ClassName(...) or top-level rule call ---

    @Override
    protected void startTyped(VmTyped value) {
      objectDepth++;
      if (value == documentModule) {
        // Top-level module as typed — no rendering needed.
        return;
      }
      if (loadLabels != null) {
        for (var annotation : value.getVmClass().getAnnotations()) {
          if (annotation.getVmClass().getQualifiedName().equals("pkl.starlark#LoadLabel")) {
            var label = (String) VmUtils.readMember(annotation, Identifier.LABEL);
            var symbol = value.getVmClass().getSimpleName();
            loadLabels.computeIfAbsent(label, k -> new LinkedHashSet<>()).add(symbol);
          }
        }
      }
      var className = value.getVmClass().getSimpleName();
      builder.append(className).append('(');
      increaseIndent();
      if (pendingRuleName != null) {
        // Render as a top-level rule call: inject name = "propName" as first argument.
        ruleCallStartDepth = objectDepth;
        if (!renderInline) {
          builder.append(LINE_BREAK).append(currIndent);
        }
        builder.append("name = \"").append(pendingRuleName).append('"');
        ruleCallHeaderWritten = true;
        pendingRuleName = null;
      }
    }

    @Override
    protected void endTyped(VmTyped value, boolean isEmpty) {
      if (value == documentModule) {
        objectDepth--;
        return;
      }
      boolean wasRuleCall = (objectDepth == ruleCallStartDepth);
      ruleCallHeaderWritten = false;
      endFunctionCall(!isEmpty || wasRuleCall);
      if (wasRuleCall) {
        ruleCallStartDepth = -1;
        builder.append(LINE_BREAK).append(LINE_BREAK);
      }
      objectDepth--;
    }

    private void endFunctionCall(boolean hasContent) {
      decreaseIndent();
      if (hasContent && !renderInline) {
        builder.append(',').append(LINE_BREAK).append(currIndent);
      }
      builder.append(')');
    }

    // --- Property handling ---

    @Override
    protected void visitProperty(Identifier name, Object value, boolean isFirst) {
      if (enclosingValue == documentModule) {
        // Top-level module property: render as a Starlark statement.
        visitTopLevelProperty(name, value);
        return;
      }

      // Inside a rule call: skip the class's own "name" property (already injected).
      if (objectDepth == ruleCallStartDepth && name.toString().equals("name")) {
        return;
      }

      // Keyword argument in a function call or struct.
      boolean needsComma = !isFirst || ruleCallHeaderWritten;
      ruleCallHeaderWritten = false;
      if (needsComma) {
        builder.append(',');
      }
      if (!renderInline) {
        builder.append(LINE_BREAK).append(currIndent);
      } else if (needsComma) {
        builder.append(' ');
      }
      builder.append(name).append(" = ");
      visit(value);
    }

    private void visitTopLevelProperty(Identifier name, Object value) {
      if (value instanceof VmTyped typedValue && !isRenderDirective(typedValue)) {
        // Class instance: render as a rule call (no assignment; endTyped adds trailing newline).
        pendingRuleName = name.toString();
        visit(value);
      } else {
        // Everything else: render as a variable assignment.
        builder.append(name).append(" = ");
        visit(value);
        builder.append(LINE_BREAK).append(LINE_BREAK);
      }
    }
  }
}
