/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import CKADocs.SourceBlock

/-!
# Blueprint Triptych Blocks

Local CKA documentation blocks for presenting paper/math, Lean, and meaning
views of a Blueprint item on the same page.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean

/-! ## Argument Parsing -/

structure CkaItemConfig where
  title : String
deriving Inhabited

structure LeanDetailConfig where
  title : Option String
deriving Inhabited

section
variable [Monad m] [MonadError m]

def CkaItemConfig.parse : ArgParse m CkaItemConfig :=
  CkaItemConfig.mk <$> .positional `title .string

def LeanDetailConfig.parse : ArgParse m LeanDetailConfig :=
  LeanDetailConfig.mk <$> ((some <$> .positional `title .string) <|> pure none)

instance : FromArgs CkaItemConfig m where
  fromArgs := CkaItemConfig.parse

instance : FromArgs LeanDetailConfig m where
  fromArgs := LeanDetailConfig.parse

end

/-! ## HTML Helpers -/

private def htmlClass (base extra : String) : Array (String × String) :=
  #[("class", base ++ " " ++ extra)]

private def panelClass (kind : String) : String :=
  "cka-triptych-panel cka-triptych-" ++ kind

private def defaultPanelTitle (kind : String) : String :=
  match kind with
  | "paper" => "Paper / Math"
  | "lean" => "Lean"
  | "meaning" => "Meaning"
  | _ => kind

/-! ## Block Extensions -/

block_extension Block.ckaItem (title : String) where
  data := toJson title
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id data contents => do
    match fromJson? (α := String) data with
    | .ok title => do
      let rendered ← contents.mapM goB
      pure <| Verso.Output.TeX.seq #[
        Verso.Output.TeX.raw ("\\subsubsection*{" ++ title ++ "}\n"),
        .seq rendered
      ]
    | .error _ => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      match fromJson? (α := String) data with
      | .ok title =>
        let body ← contents.mapM goB
        pure <|
          Verso.Output.Html.tag "section" #[
            ("class", "cka-triptych"),
            ("data-cka-triptych", "true")
          ] <| .seq #[
            Verso.Output.Html.tag "h3" #[
              ("class", "cka-triptych-title")
            ] (Verso.Output.Html.text true title),
            Verso.Output.Html.tag "div" #[
              ("class", "cka-triptych-grid")
            ] (.seq body)
          ]
      | .error _ => contents.mapM goB

block_extension Block.ckaPanel (kind : String) (title : String) where
  data := toJson (kind, title)
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id data contents => do
    match fromJson? (α := String × String) data with
    | .ok (_kind, title) => do
      let rendered ← contents.mapM goB
      pure <| Verso.Output.TeX.seq #[
        Verso.Output.TeX.raw ("\\paragraph{" ++ title ++ "}\n"),
        .seq rendered
      ]
    | .error _ => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      match fromJson? (α := String × String) data with
      | .ok (kind, title) =>
        let body ← contents.mapM goB
        pure <|
          Verso.Output.Html.tag "section" (htmlClass (panelClass kind) "") <| .seq #[
            Verso.Output.Html.tag "h4" #[
              ("class", "cka-triptych-panel-title")
            ] (Verso.Output.Html.text true title),
            Verso.Output.Html.tag "div" #[
              ("class", "cka-triptych-panel-body")
            ] (.seq body)
          ]
      | .error _ => contents.mapM goB

block_extension Block.leanDetail (title : String) where
  data := toJson title
  traverse _id _data _contents := do
    pure none
  toTeX := some <| fun _goI goB _id _data contents => contents.mapM goB
  toHtml :=
    some <| fun _goI goB _id data contents => do
      let title :=
        match fromJson? (α := String) data with
        | .ok title => title
        | .error _ => "Lean detail"
      let body ← contents.mapM goB
      pure <|
        Verso.Output.Html.tag "details" #[
          ("class", "cka-lean-detail")
        ] <| .seq #[
          Verso.Output.Html.tag "summary" #[
            ("class", "cka-lean-detail-summary")
          ] (Verso.Output.Html.text true title),
          Verso.Output.Html.tag "div" #[
            ("class", "cka-lean-detail-inner")
          ] <| .seq #[
            Verso.Output.Html.tag "section" #[
              ("class", "cka-lean-detail-source")
            ] (.seq body)
          ]
        ]

/-! ## Directives -/

@[directive]
def ckaItem : DirectiveExpanderOf CkaItemConfig
  | cfg, contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other (Block.ckaItem $(quote cfg.title)) #[$contents,*])

private meta def panelDirective (kind title : String) :
    DirectiveExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM Elab.elabBlock
    ``(Block.other (Block.ckaPanel $(quote kind) $(quote title)) #[$contents,*])

@[directive]
def ckaPaper : DirectiveExpanderOf Unit :=
  panelDirective "paper" (defaultPanelTitle "paper")

@[directive]
def ckaLean : DirectiveExpanderOf Unit :=
  panelDirective "lean" (defaultPanelTitle "lean")

@[directive]
def ckaMeaning : DirectiveExpanderOf Unit :=
  panelDirective "meaning" (defaultPanelTitle "meaning")

@[directive]
def leanDetail : DirectiveExpanderOf LeanDetailConfig
  | cfg, contents => do
    let contents ← contents.mapM Elab.elabBlock
    let title := cfg.title.getD "Lean source"
    ``(Block.other (Block.leanDetail $(quote title)) #[$contents,*])
