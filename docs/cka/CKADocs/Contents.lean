/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary

import CKADocs.SourceBlock
import CKADocs.DocIntro
import CKADocs.DocVCVioOracles
import CKADocs.DocFigure3Correspondence
import CKADocs.DocGameState
import CKADocs.DocDDHConstruction
import CKADocs.DocSecurityTheorem3
import CKADocs.DocCorrespondenceIndex

/-!
# CKA Docs Contents

Blueprint root for the CKA paper-to-code documentation.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "CKA from DDH in VCV-io" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "CKA from DDH"
%%%

This site documents the current `Examples/CKA` formalization of continuous key
agreement from DDH. Its purpose is paper-to-code correspondence: the reader
should be able to put the paper's Figure 3 and Theorem 3 next to the Lean files
and see exactly how each concept was translated.

The source of truth is Alwen, Coretti, and Dodis, "The Double Ratchet:
Security Notions, Proofs, and Modularization for the Signal Protocol",
Section 4.1, Figure 3, and Theorem 3.

{include 1 CKADocs.DocIntro}
{include 1 CKADocs.DocVCVioOracles}
{include 1 CKADocs.DocFigure3Correspondence}
{include 1 CKADocs.DocGameState}
{include 1 CKADocs.DocDDHConstruction}
{include 1 CKADocs.DocSecurityTheorem3}
{include 1 CKADocs.DocCorrespondenceIndex}

{blueprint_graph}

{blueprint_summary}

