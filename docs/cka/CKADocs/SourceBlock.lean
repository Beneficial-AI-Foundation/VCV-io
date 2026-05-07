/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import SubVerso.Highlighting.String

/-!
# Source Block Helper

Custom Verso helpers for extracting selected source bodies from live Lean
declarations.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean
open SubVerso.Highlighting

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

public structure SourceConfig where
  name : Ident
deriving Inhabited

public structure ExtractedSource where
  moduleName : Name
  source : String

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

private def isDeclHeaderLine (line : String) : Bool :=
  let line := line.trimAsciiStart.toString
  let prefixes := #[
    "def ", "noncomputable def ", "private def ", "private noncomputable def ",
    "theorem ", "private theorem ", "lemma ", "private lemma ",
    "structure ", "class ", "inductive ", "abbrev ", "instance ", "opaque ", "axiom "
  ]
  prefixes.any (fun p => line.startsWith p)

private def findDeclHeaderStart (lines : List String) (startIdx endLine : Nat) : Nat := Id.run do
  let lines := lines.toArray
  if lines.isEmpty then
    return startIdx
  let start := Nat.min startIdx (lines.size - 1)
  let upper := Nat.min (endLine - 1) (lines.size - 1)
  if start <= upper then
    for idx in [start:upper + 1] do
      if isDeclHeaderLine lines[idx]! then
        return idx
  for offset in [:start + 1] do
    let idx := start - offset
    if isDeclHeaderLine lines[idx]! then
      return idx
  return startIdx

public def extractProofBody (source : String) : String :=
  if let some idx := findSubstring source ":= by" then
    "by" ++ (source.drop (idx + ":= by".length)).toString
  else if (findSubstring source " where").isSome then
    source
  else if let some idx := findSubstring source ":= " then
    (source.drop (idx + ":= ".length)).toString
  else
    source

public meta def extractDeclBody (declName : Name) : DocElabM ExtractedSource := do
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
  let startIdx := findDeclHeaderStart lines (startLine - 1) endLine
  let selected := lines.drop startIdx |>.take (endLine - startIdx)
  let fullSource := "\n".intercalate selected
  pure {
    moduleName := modName
    source := fullSource.trimAscii.toString
  }

private meta def readModuleSource (moduleName : Name) : DocElabM String := do
  let parts := moduleName.components.map (·.toString)
  let relPath := String.intercalate "/" parts ++ ".lean"
  let candidates : List System.FilePath := [relPath, ".." / ".." / relPath]
  let some path ← candidates.findM? (·.pathExists)
    | throwError s!"source: source file not found (tried {candidates})"
  IO.FS.readFile path

private def isSupportSourceEndLine (line : String) : Bool :=
  let line := line.trimAsciiStart.toString
  line.startsWith "/--" ||
    line.startsWith "/-!" ||
    line.startsWith "omit " ||
    isDeclHeaderLine line

private def findSourceByHeader? (lines : List String) (header : String) : Option String := Id.run do
  let lines := lines.toArray
  let mut start? := none
  for idx in [:lines.size] do
    if lines[idx]!.trimAsciiStart.toString.startsWith header then
      start? := some idx
      break
  let some start := start?
    | return none

  let mut stop := lines.size
  for idx in [start + 1:lines.size] do
    if isSupportSourceEndLine lines[idx]! then
      stop := idx
      break
  pure <| some <| "\n".intercalate ((lines.toList.drop start).take (stop - start)) |>.trimAscii.toString

private def supportHeadersFor? (declName : Name) : Option (List String) :=
  if declName.toString == "ddhCKA.securityReduction" then
    some [
      "private noncomputable def reductionSendB",
      "private noncomputable def reductionSendA",
      "private noncomputable def reductionChallA",
      "private noncomputable def reductionChallB",
      "private noncomputable def reductionOracleImpl",
      "private noncomputable def reductionInitState"
    ]
  else
    none

private meta def supportSourcePrefix? (declName moduleName : Name) : DocElabM (Option String) := do
  let some headers := supportHeadersFor? declName
    | pure none
  let contents ← readModuleSource moduleName
  let lines := contents.splitOn "\n"
  let mut pieces : List String := []
  let mut foundAll := true
  for header in headers do
    match findSourceByHeader? lines header with
    | some source => pieces := pieces.concat source
    | none => foundAll := false
  if foundAll then
    pure <| some <| "\n\n".intercalate pieces
  else
    pure none

private def isPreviewableSource (source : String) : Bool :=
  let source := source.trimAsciiStart.toString
  let prefixes := #[
    "def ", "noncomputable def ", "private def ", "private noncomputable def ",
    "abbrev ", "structure ", "inductive "
  ]
  let dependsOnPrivateLocalHelper :=
    (findSubstring source "reductionInitState").isSome ||
    (findSubstring source "reductionOracleImpl").isSome
  source.length ≤ 50000 &&
    !dependsOnPrivateLocalHelper &&
    prefixes.any (source.startsWith ·)

private def isTheoremLikeSource (source : String) : Bool :=
  let source := source.trimAsciiStart.toString
  let prefixes := #[
    "theorem ", "private theorem ", "lemma ", "private lemma "
  ]
  prefixes.any (source.startsWith ·)

private def theoremStatementSource? (source : String) : Option String :=
  let source := source.trimAscii.toString
  let stop? :=
    match findSubstring source ":= by" with
    | some idx => some idx
    | none => findSubstring source ":="
  stop?.map fun idx => (source.take idx).trimAscii.toString

private def sanitizeNamespacePart (s : String) : String :=
  let chars := s.toList.map fun c =>
    if c.isAlphanum then c else '_'
  let s := String.ofList chars
  if s.isEmpty || s.front.isDigit then "decl_" ++ s else s

private def previewNamespace (declName : Name) : String :=
  let parts := declName.components.map (sanitizeNamespacePart ·.toString)
  "CKADocs.SourcePreview." ++ String.intercalate "_" parts

private def previewPrefix (moduleName declName : Name) : String :=
  let ns := previewNamespace declName
  let ddhOpen :=
    if (moduleName.toString.splitOn ".").contains "FromDDH" then
      "open ddhCKA DiffieHellman\n"
    else
      ""
  let ddhVars :=
    if (moduleName.toString.splitOn ".").contains "FromDDH" then
      "variable [DecidableEq G]\n"
    else
      ""
  s!"namespace {ns}\n" ++
  "open CKAScheme\n" ++
  ddhOpen ++
  "open OracleSpec OracleComp ENNReal\n" ++
  "variable {IK St I Rho : Type}\n" ++
  "variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]\n" ++
  "variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]\n" ++
  ddhVars ++
  "\n"

private def theoremPreviewPrefix (moduleName declName : Name) : String :=
  previewPrefix moduleName declName ++
  "variable {gen : G}\n" ++
  "axiom ckaDocsProof {p : Prop} : p\n\n"

private def previewSuffix (declName : Name) : String :=
  s!"\nend {previewNamespace declName}\n"

private def isSourceStartKeyword (s : String) : Bool :=
  #["private", "noncomputable", "def", "abbrev", "structure", "inductive",
    "theorem", "lemma"].contains s

private def isKeywordLeaf (p : String → Bool) : Highlighted → Bool
  | .token ⟨.keyword .., content⟩ => p content.trimAscii.toString
  | _ => false

private def isAnyKeywordLeaf : Highlighted → Bool
  | .token ⟨.keyword .., _⟩ => true
  | _ => false

private def isTokenLeaf (p : String → Bool) : Highlighted → Bool
  | .token ⟨_, content⟩ => p content.trimAscii.toString
  | _ => false

private partial def flattenHighlightedLeaves : Highlighted → Array Highlighted
  | .seq xs => xs.foldl (init := #[]) fun acc x => acc ++ flattenHighlightedLeaves x
  | .span _ content => flattenHighlightedLeaves content
  | .tactics _ _ _ content => flattenHighlightedLeaves content
  | leaf => #[leaf]

private def tokenText? : Highlighted → Option String
  | .token ⟨_, content⟩ => some content.trimAscii.toString
  | _ => none

private def isProjectionTarget? (leaf : Highlighted) : Bool :=
  match tokenText? leaf with
  | some "toReal" => true
  | some "run" => true
  | _ => false

private def isProjectionDotGlitch (text : String) : Bool :=
  text == "" || text == "f" || text == "e" || text == "l" || text == "/"

private def normalizeProjectionDots (leaves : Array Highlighted) : Array Highlighted :=
  leaves.mapIdx fun idx leaf =>
    match leaf with
    | .token ⟨kind, content⟩ =>
      let text := content.trimAscii.toString
      if isProjectionDotGlitch text && leaves[idx + 1]?.any isProjectionTarget? then
        .token ⟨kind, "."⟩
      else
        leaf
    | _ => leaf

private def firstIndex? (xs : Array α) (p : α → Bool) : Option Nat := Id.run do
  for i in [:xs.size] do
    match xs[i]? with
    | some x =>
      if p x then
        return some i
    | none => pure ()
  return none

private def lastIndex? (xs : Array α) (p : α → Bool) : Option Nat := Id.run do
  for i in [:xs.size] do
    let idx := xs.size - 1 - i
    match xs[idx]? with
    | some x =>
      if p x then
        return some idx
    | none => pure ()
  return none

private partial def prevKeywordIndex? (leaves : Array Highlighted) (idx : Nat) : Option Nat :=
  if idx == 0 then
    none
  else
    let idx := idx - 1
    match leaves[idx]? with
    | some leaf =>
      if isAnyKeywordLeaf leaf then some idx else prevKeywordIndex? leaves idx
    | none => none

private def isDeclPrimaryKeyword (s : String) : Bool :=
  #["def", "abbrev", "structure", "inductive", "theorem", "lemma"].contains s

private def isDeclModifierKeyword (s : String) : Bool :=
  #["private", "noncomputable"].contains s

private partial def rewindDeclModifiers (leaves : Array Highlighted) (idx : Nat) : Nat :=
  match prevKeywordIndex? leaves idx with
  | some prev =>
    match leaves[prev]? with
    | some leaf =>
      if isKeywordLeaf isDeclModifierKeyword leaf then
        rewindDeclModifiers leaves prev
      else
        idx
    | none => idx
  | none => idx

private def trimHighlightedWrapper (highlighted : Highlighted) : Highlighted :=
  let leaves := flattenHighlightedLeaves highlighted
  let start := (firstIndex? leaves (isKeywordLeaf isSourceStartKeyword)).getD 0
  let leaves := leaves.extract start leaves.size
  let stop := (lastIndex? leaves (isKeywordLeaf (· == "end"))).getD leaves.size
  .seq (normalizeProjectionDots (leaves.extract 0 stop))

private def trimHighlightedWrapperFromLastDecl (highlighted : Highlighted) : Highlighted :=
  let leaves := flattenHighlightedLeaves highlighted
  let primary := (lastIndex? leaves (isKeywordLeaf isDeclPrimaryKeyword)).getD 0
  let start := rewindDeclModifiers leaves primary
  let leaves := leaves.extract start leaves.size
  let stop := (lastIndex? leaves (isKeywordLeaf (· == "end"))).getD leaves.size
  .seq (normalizeProjectionDots (leaves.extract 0 stop))

private def trimStatementHighlightedWrapper (highlighted : Highlighted) : Highlighted :=
  let leaves := flattenHighlightedLeaves highlighted
  let start := (firstIndex? leaves (isKeywordLeaf isSourceStartKeyword)).getD 0
  let leaves := leaves.extract start leaves.size
  let stop := (firstIndex? leaves (isTokenLeaf (· == ":="))).getD leaves.size
  .seq (normalizeProjectionDots (leaves.extract 0 stop))

block_extension Block.leanSource (declName : String) (source : String) where
  data := toJson (declName, source)
  traverse _id _data _contents := do
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        pure <| .raw ("\\paragraph{Lean source: " ++ declName ++ "}\\begin{verbatim}\n" ++
          source ++ "\n\\end{verbatim}\n")
      | .error _ => pure .empty
  toHtml :=
    some <| fun _goI goB _id data contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        let rendered ← contents.mapM goB
        let title := s!"Lean source: {declName}"
        let body :=
          if contents.isEmpty then
            Verso.Output.Html.tag "pre" #[
              ("class", "cka-lean-source-code")
            ] (Verso.Output.Html.text true source)
          else
            Verso.Output.Html.tag "div" #[
              ("class", "cka-lean-source-rendered")
            ] (.seq rendered)
        pure <|
          Verso.Output.Html.tag "section" #[
            ("class", "cka-lean-source")
          ] <| .seq #[
            Verso.Output.Html.tag "div" #[
              ("class", "cka-lean-source-summary")
            ] (Verso.Output.Html.text true title),
            body
          ]
      | .error _ => pure .empty

block_extension Block.leanStatement (declName : String) (source : String) where
  data := toJson (declName, source)
  traverse _id _data _contents := do
    pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        pure <| .raw ("\\paragraph{Lean statement: " ++ declName ++ "}\\begin{verbatim}\n" ++
          source ++ "\n\\end{verbatim}\n")
      | .error _ => pure .empty
  toHtml :=
    some <| fun _goI goB _id data contents => do
      match fromJson? (α := String × String) data with
      | .ok (declName, source) =>
        let rendered ← contents.mapM goB
        let title := s!"Lean statement: {declName}"
        let body :=
          if contents.isEmpty then
            Verso.Output.Html.tag "pre" #[
              ("class", "cka-lean-source-code")
            ] (Verso.Output.Html.text true source)
          else
            Verso.Output.Html.tag "div" #[
              ("class", "cka-lean-source-rendered")
            ] (.seq rendered)
        pure <|
          Verso.Output.Html.tag "section" #[
            ("class", "cka-lean-source cka-lean-statement")
          ] <| .seq #[
            Verso.Output.Html.tag "div" #[
              ("class", "cka-lean-source-summary")
            ] (Verso.Output.Html.text true title),
            body
          ]
      | .error _ => pure .empty

private meta def sourcePreviewTerm? (declName moduleName : Name) (source : String) :
    DocElabM (Option Term) := do
  let support? ← supportSourcePrefix? declName moduleName
  if isPreviewableSource source || support?.isSome then
    let pre := previewPrefix moduleName declName
    let post := previewSuffix declName
    let supportPrefix := support?.map (· ++ "\n\n") |>.getD ""
    let wrapped : StrLit := Syntax.mkStrLit (pre ++ supportPrefix ++ source ++ post)
    let cfg : Verso.Genre.Manual.InlineLean.LeanBlockConfig := {
      «show» := true
      keep := false
      name := none
      error := false
      fresh := false
    }
    try
      let term ←
        Verso.Genre.Manual.InlineLean.elabCommands cfg wrapped
          (fun _shouldShow highlighted _str => do
            let highlighted :=
              if support?.isSome then
                trimHighlightedWrapperFromLastDecl highlighted
              else
                trimHighlightedWrapper highlighted
            ``(Block.other (_root_.Block.leanSource $(quote declName.toString) $(quote source)) #[
                Block.other
                  (Verso.Genre.Manual.InlineLean.Block.lean
                    $(quote highlighted)
                    (none : Option System.FilePath)
                    (none : Option Lean.Lsp.Range))
                  #[]
              ]))
      pure (some term)
    catch
      | _ => pure none
  else
    pure none

private meta def statementPreviewTerm? (declName moduleName : Name) (statement : String) :
    DocElabM (Option Term) := do
  let pre := theoremPreviewPrefix moduleName declName
  let post := previewSuffix declName
  let wrapped : StrLit := Syntax.mkStrLit (pre ++ statement ++ " := ckaDocsProof" ++ post)
  let cfg : Verso.Genre.Manual.InlineLean.LeanBlockConfig := {
    «show» := true
    keep := false
    name := none
    error := false
    fresh := false
  }
  try
    let term ←
      Verso.Genre.Manual.InlineLean.elabCommands cfg wrapped
        (fun _shouldShow highlighted _str => do
          let highlighted := trimStatementHighlightedWrapper highlighted
          ``(Block.other (_root_.Block.leanStatement $(quote declName.toString) $(quote statement)) #[
              Block.other
                (Verso.Genre.Manual.InlineLean.Block.lean
                  $(quote highlighted)
                  (none : Option System.FilePath)
                  (none : Option Lean.Lsp.Range))
                #[]
            ]))
    pure (some term)
  catch
    | _ => pure none

private meta def sourceBlockTerm (cfg : SourceConfig) : DocElabM Term := do
  let declName := cfg.name.getId
  let extracted ← extractDeclBody declName
  if isTheoremLikeSource extracted.source then
    let statement := (theoremStatementSource? extracted.source).getD extracted.source
    let preview? ← statementPreviewTerm? declName extracted.moduleName statement
    match preview? with
    | some term => pure term
    | none =>
      ``(Block.other (Block.leanStatement $(quote declName.toString) $(quote statement)) #[])
  else
    let preview? ← sourcePreviewTerm? declName extracted.moduleName extracted.source
    match preview? with
    | some term => pure term
    | none =>
      ``(Block.other (Block.leanSource $(quote declName.toString) $(quote extracted.source)) #[])

/--
Extracts a live Lean declaration and renders it as a CKA-local source panel.
Definitions render as source. Theorems and lemmas render as interactive
statements only; readers can open the Lean file for proof terms.
-/
@[code_block]
meta def leanSource : SourceConfig → StrLit → DocElabM Term
  | cfg, _code => sourceBlockTerm cfg

/--
Backward-compatible spelling for older CKA docs. New pages should prefer
`leanSource`.
-/
@[code_block]
meta def source : SourceConfig → StrLit → DocElabM Term
  | cfg, _code => sourceBlockTerm cfg
