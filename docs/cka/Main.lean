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

.proof-source-code {
  margin: 0;
  padding: 0.8rem 1rem;
  font-family: monospace;
  font-size: 0.88em;
  line-height: 1.6;
  white-space: pre;
  overflow-x: auto;
  color: #24292E;
  background: var(--bp-color-surface-muted, #f8fafc);
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

.bp_code_panel_wrapper {
  display: none !important;
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
    var markerText = '-- PROOF-SOURCE';
    document.querySelectorAll('pre').forEach(function(el) {
      var text = el.textContent || '';
      if (text.trimStart().indexOf(markerText) !== 0) return;
      var idx = text.indexOf(markerText);
      var rest = text.substring(idx + markerText.length);
      var nlIdx = rest.indexOf('\n');
      var code = nlIdx >= 0 ? rest.substring(nlIdx + 1) : rest;
      el.classList.add('proof-source-code');
      el.textContent = code;
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
