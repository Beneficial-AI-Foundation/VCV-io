/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual

/-!
# Source Block Helper

Custom Verso block for displaying selected source bodies from live Lean
declarations.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean

/-! ## Local Documentation Blocks -/

structure DocH2Config where
  title : String
deriving Inhabited

section
variable [Monad m] [MonadError m]

def DocH2Config.parse : ArgParse m DocH2Config :=
  DocH2Config.mk <$> .positional `title .string

instance : FromArgs DocH2Config m where
  fromArgs := DocH2Config.parse

end

open Verso Doc Elab Genre Manual in
block_extension Block.docH2 (title : String) where
  data := toJson title
  traverse _id _data _contents := do
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String) data with
      | .ok title => pure <| .raw ("\\subsection*{" ++ title ++ "}\n")
      | .error _ => pure .empty
  toHtml :=
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String) data with
      | .ok title =>
        pure <|
          Verso.Output.Html.tag "h2" #[
            ("class", "ckadocs-doc-h2"),
            ("style", "margin-top:2.25rem;padding-top:1rem;border-top:1px solid #d8dee8;")
          ]
            (Verso.Output.Html.text true title)
      | .error _ => pure .empty

/--
Renders an HTML `h2`-style heading without creating a Verso section or
Blueprint node.
-/
@[block_command]
meta def docH2 : BlockCommandOf DocH2Config
  | cfg => ``(Block.other (Block.docH2 $(quote cfg.title)) #[])

/-! ## Source Extraction -/

structure SourceConfig where
  name : Ident
deriving Inhabited

instance : FromArgs SourceConfig DocElabM :=
  ⟨SourceConfig.mk <$> positional' (α := Ident) `name⟩

private def findSubstring (haystack needle : String) : Option Nat := Id.run do
  let hLen := haystack.length
  let nLen := needle.length
  if nLen > hLen then
    return none
  for i in [:hLen - nLen + 1] do
    if (haystack.drop i).startsWith needle then
      return some i
  return none

private def extractProofBody (source : String) : String :=
  if let some idx := findSubstring source ":= by" then
    "by" ++ (source.drop (idx + ":= by".length)).toString
  else if let some idx := findSubstring source ":= " then
    (source.drop (idx + ":= ".length)).toString
  else
    source

@[code_block]
meta def source : SourceConfig → StrLit → DocElabM Term
  | cfg, _code => do
    let declName := cfg.name.getId
    let some ranges ← findDeclarationRanges? declName
      | throwError s!"source: declaration '{declName}' not found or has no source range"

    let env ← getEnv
    let some modIdx := env.getModuleIdxFor? declName
      | throwError s!"source: could not find module for '{declName}'"
    let modName := env.header.moduleNames[modIdx.toNat]!

    let parts := modName.components.map (·.toString)
    let relPath := String.intercalate "/" parts ++ ".lean"
    let candidates : List System.FilePath := [relPath, ".." / ".." / relPath]
    let some path ← candidates.findM? (·.pathExists)
      | throwError s!"source: source file not found (tried {candidates})"

    let contents ← IO.FS.readFile path
    let lines := contents.splitOn "\n"
    let startLine := ranges.range.pos.line
    let endLine := ranges.range.endPos.line
    let selected := lines.drop startLine |>.take (endLine - startLine + 1)
    let fullSource := "\n".intercalate selected
    let proofBody := (extractProofBody fullSource).trimAscii.toString
    let markedCode := "-- PROOF-SOURCE\n" ++ proofBody
    ``(Block.code $(quote markedCode))
