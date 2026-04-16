/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary

import DoubleRatchetDocs.DocIntro
import DoubleRatchetDocs.DocCryptoPrimer
import DoubleRatchetDocs.DocCKA
import DoubleRatchetDocs.DocFigure3
import DoubleRatchetDocs.DocDDHCKA
import DoubleRatchetDocs.DocReduction
import DoubleRatchetDocs.DocTheorem3
import DoubleRatchetDocs.DocAsymptoticSecurity
import DoubleRatchetDocs.DocCorrespondence

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Double Ratchet in Lean" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "Double Ratchet in Lean"
%%%

A Lean 4 formalization of the Continuous Key Agreement part of
"The Double Ratchet: Security Notions, Proofs, and Modularization for the
Signal Protocol" by Alwen, Coretti, and Dodis.

The current formalization centers on the DDH-based CKA construction and on the
paper's Theorem 3. The documentation is paper-faithful first: it explains the
cryptographic game, then shows how the Lean code encodes the same semantics.
Auxiliary single-epoch and restricted multi-epoch layers are documented, but
they are marked as support infrastructure rather than as the canonical theorem
surface.

{include 1 DoubleRatchetDocs.DocIntro}
{include 1 DoubleRatchetDocs.DocCryptoPrimer}
{include 1 DoubleRatchetDocs.DocCKA}
{include 1 DoubleRatchetDocs.DocFigure3}
{include 1 DoubleRatchetDocs.DocDDHCKA}
{include 1 DoubleRatchetDocs.DocReduction}
{include 1 DoubleRatchetDocs.DocTheorem3}
{include 1 DoubleRatchetDocs.DocAsymptoticSecurity}
{include 1 DoubleRatchetDocs.DocCorrespondence}

{blueprint_graph}

{blueprint_summary}
