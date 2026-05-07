/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.Contents

/-!
# CKA Docs Renderer

Verso renderer entry point for the CKA documentation site.
-/

open Verso.Genre Manual
open Informal

def ckaDocsCss : CSS := CSS.mk
r#"
:root {
  --verso-code-keyword-color: #D73A49;
  --verso-code-keyword-weight: normal;
}

.hl.lean .keyword { color: #D73A49; }
.hl.lean .var { color: #24292E; }
.hl.lean .const { color: #6F42C1; }
.hl.lean .sort { color: #005CC5; }
.hl.lean .literal { color: #005CC5; }
.hl.lean .string { color: #032F62; }
.hl.lean .unknown { color: #24292E; }
.hl.lean .inter-text { color: #24292E; }

.bp_external_decl_body .docstring {
  font-family: var(--verso-text-font-family, sans-serif);
  font-size: 0.95em;
  line-height: 1.5;
  white-space: normal;
  padding: 0.6rem 0.8rem;
  margin: 0.4rem 0 0 0;
  background: #f8fafc;
  border-left: 3px solid #2563eb;
  border-radius: 0 4px 4px 0;
}

.katex-display {
  max-width: 100%;
  overflow-x: auto;
  overflow-y: hidden;
  padding: 0.15rem 0;
}

.bp_math.display {
  display: block;
  max-width: 100%;
  overflow-x: auto;
}

.cka-game-grid {
  display: grid;
  grid-template-columns: repeat(2, minmax(0, 1fr));
  gap: 0.85rem 1rem;
  align-items: start;
  margin: 1rem 0;
}

.cka-game-grid > * {
  min-width: 0;
}

.cka-game-cell {
  overflow: hidden;
  border: 1px solid #334155;
  border-radius: 4px;
  background: #ffffff;
}

.cka-game-cell[data-kind="game"],
.cka-game-cell[data-kind="challenge"],
.cka-game-cell[data-kind="security"] {
  grid-column: 1 / -1;
}

.cka-game-cell-header {
  padding: 0.45rem 0.7rem;
  border-bottom: 1px solid currentColor;
  background: #e8eefc;
  color: #1f2937;
  font-weight: 700;
  line-height: 1.25;
}

.cka-game-cell[data-kind="oracle"] {
  border-color: #3f7a5a;
}

.cka-game-cell[data-kind="oracle"] .cka-game-cell-header {
  background: #edf6f0;
  color: #3f7a5a;
}

.cka-game-cell[data-kind="challenge"] {
  border-color: #2563eb;
}

.cka-game-cell[data-kind="challenge"] .cka-game-cell-header {
  background: #eaf1ff;
  color: #2563eb;
}

.cka-game-cell[data-kind="corrupt"] {
  border-color: #dc2626;
}

.cka-game-cell[data-kind="corrupt"] .cka-game-cell-header {
  background: #fdecec;
  color: #dc2626;
}

.cka-game-cell[data-kind="security"] {
  border-color: #64748b;
}

.cka-game-cell-body {
  padding: 0.65rem 0.75rem;
}

.cka-game-cell-body p {
  margin: 0.18rem 0;
}

.cka-game-cell-body .bp_math.inline {
  white-space: normal;
}

.cka-game-grid .katex-display,
.cka-msc .katex-display {
  margin: 0;
  text-align: left;
}

.cka-game-grid .katex-display > .katex,
.cka-msc .katex-display > .katex {
  text-align: left;
  white-space: normal;
}

.cka-game-grid .bp_math.display,
.cka-msc .bp_math.display {
  overflow-x: visible;
}

.cka-msc {
  margin: 1rem 0;
  max-width: 100%;
  overflow-x: auto;
}

.cka-msc .katex-display .katex {
  font-size: 0.95em;
}

@media (max-width: 900px) {
  .cka-game-grid {
    grid-template-columns: minmax(0, 1fr);
  }
}

.bp_name {
  font-weight: bold;
  font-style: italic;
  white-space: nowrap;
}

.bp_heading_title_row_statement {
  display: inline-flex !important;
  align-items: baseline;
  gap: 0.35rem;
  white-space: nowrap;
}

.cka-triptych {
  margin: 1.25rem 0 1.5rem;
}

.cka-triptych-title {
  margin: 0 0 0.75rem;
  font-size: 1.05rem;
  line-height: 1.35;
  letter-spacing: 0;
}

.cka-triptych-grid {
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 0.85rem;
  align-items: start;
}

.cka-triptych-panel {
  min-width: 0;
  padding: 0.85rem 0.9rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #ffffff;
}

.cka-triptych-paper {
  border-top: 3px solid #0f766e;
}

.cka-triptych-lean {
  border-top: 3px solid #2563eb;
}

.cka-triptych-meaning {
  border-top: 3px solid #7c3aed;
}

.cka-triptych-panel-title {
  margin: 0 0 0.55rem;
  color: #334155;
  font-size: 0.78rem;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.cka-triptych-panel-body > :first-child {
  margin-top: 0;
}

.cka-triptych-panel-body > :last-child {
  margin-bottom: 0;
}

.cka-triptych pre,
.cka-lean-source-code,
.cka-lean-source-rendered pre {
  max-width: 100%;
  white-space: pre-wrap;
  overflow-x: auto;
  overflow-wrap: anywhere;
}

.bp_external_decl_rendered pre {
  max-width: 100%;
  white-space: pre;
  overflow-x: auto;
  overflow-wrap: normal;
}

.cka-lean-detail {
  margin-top: 0.8rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #f8fafc;
}

.cka-lean-detail-summary {
  cursor: pointer;
  padding: 0.55rem 0.7rem;
  font-weight: 600;
  color: #1e293b;
}

.cka-lean-detail-inner {
  padding: 0 0.7rem 0.7rem;
}

.cka-lean-detail-heading {
  margin: 0.65rem 0 0.35rem;
  color: #475569;
  font-size: 0.78rem;
  font-weight: 700;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.cka-lean-source {
  margin-top: 0.35rem;
  border: 1px solid #d8dee8;
  border-radius: 6px;
  background: #ffffff;
}

.cka-lean-source-summary {
  padding: 0.55rem 0.7rem;
  color: #334155;
  font-size: 0.82rem;
  font-weight: 700;
  line-height: 1.25;
  letter-spacing: 0;
  text-transform: uppercase;
}

.cka-lean-source-rendered {
  border-top: 1px solid #e2e8f0;
}

.cka-lean-source-rendered .examples {
  margin: 0;
  border: 0;
  border-left: 3px solid #2563eb;
  border-radius: 0 0 6px 6px;
  background: #f8fafc;
}

.cka-lean-source-rendered code.hl.lean.block {
  display: block;
  max-width: 100%;
  margin: 0;
  padding: 0.75rem 0.85rem;
  color: #24292E;
  background: #f8fafc;
  border: 0;
  border-left: 3px solid #2563eb;
  border-radius: 0 0 6px 6px;
  overflow-x: auto;
  overflow-wrap: anywhere;
  white-space: pre-wrap;
  font-family: monospace;
  font-size: 0.86em;
  line-height: 1.55;
}

.cka-lean-source-code {
  margin: 0;
  padding: 0.75rem 0.85rem;
  color: #24292E;
  background: #f8fafc;
  border: 0;
  border-left: 3px solid #2563eb;
  border-radius: 0 0 6px 6px;
  font-family: monospace;
  font-size: 0.86em;
  line-height: 1.55;
}

.bp_external_decl_rendered {
  max-width: 100%;
  overflow-x: auto;
  overflow-y: visible;
}

.bp_external_decl_rendered .bp_external_decl_body {
  overflow-wrap: anywhere;
}

.bp_code_panel_wrapper {
  display: none !important;
}

.tippy-box[data-theme~='lean'] .hover-info {
  display: block !important;
  position: static !important;
  transform: none !important;
  background: transparent !important;
  border: 0 !important;
  padding: 0 !important;
}

.tippy-box[data-theme~='lean'] .hover-info code {
  display: block;
  white-space: pre-wrap;
}
"#

def ckaDocsJs : JS := JS.mk
r#"
(function() {
  function onReady(fn) {
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', fn);
    } else {
      fn();
    }
  }

  onReady(function() {
    document.querySelectorAll('.bp_heading_title_row_statement').forEach(function(row) {
      if (row.querySelector('.bp_name')) return;
      var caption = row.querySelector('.bp_caption[title]');
      if (!caption) return;
      var name = caption.getAttribute('title');
      if (!name || name.length === 0) return;
      var nameSpan = document.createElement('span');
      nameSpan.className = 'bp_name';
      nameSpan.textContent = '(' + name + ')';
      row.appendChild(nameSpan);
    });
  });

  onReady(function() {
    document.documentElement.setAttribute('data-bp-style', 'modern');
  });

  onReady(function() {
    document.querySelectorAll('.cka-lean-source-rendered code.hl.lean.block').forEach(function(code) {
      if (code.dataset.ckaSourceTrimmed) return;
      var nodes = Array.prototype.slice.call(code.childNodes);
      var sourceStart = -1;
      for (var i = 0; i < nodes.length; i++) {
        var node = nodes[i];
        if (node.nodeType === Node.ELEMENT_NODE &&
            node.classList.contains('keyword') &&
            /^(private|noncomputable|def|abbrev|structure|inductive)$/.test(node.textContent.trim())) {
          sourceStart = i;
          break;
        }
      }
      if (sourceStart > 0) {
        for (var j = 0; j < sourceStart; j++) nodes[j].remove();
      }

      nodes = Array.prototype.slice.call(code.childNodes);
      var sourceEnd = -1;
      for (var k = nodes.length - 1; k >= 0; k--) {
        var endNode = nodes[k];
        if (endNode.nodeType === Node.ELEMENT_NODE &&
            endNode.classList.contains('keyword') &&
            endNode.textContent.trim() === 'end') {
          sourceEnd = k;
          break;
        }
      }
      if (sourceEnd >= 0) {
        for (var l = sourceEnd; l < nodes.length; l++) nodes[l].remove();
      }
      code.dataset.ckaSourceTrimmed = 'true';
    });
  });

  onReady(function() {
    document.querySelectorAll('.bp_code_panel_wrapper').forEach(function(panel) {
      var block = panel.previousElementSibling;
      while (block && !(block.classList && block.classList.contains('bp_wrapper'))) {
        block = block.previousElementSibling;
      }
      if (!block) return;
      if (!block.querySelector('.cka-triptych')) return;
      panel.classList.add('cka-triptych-blueprint-panel');
    });
  });
})();
"#

def main (args : List String) : IO UInt32 :=
  PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc CKADocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := {
      toHtmlAssets := {
        features := .all
        extraCss := .ofList [ckaDocsCss]
        extraJs := .ofList [ckaDocsJs]
      }
    })
