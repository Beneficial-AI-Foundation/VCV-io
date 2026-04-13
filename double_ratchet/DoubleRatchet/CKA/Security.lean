/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.SecurityGame

/-!
# CKA Security Definition

Auxiliary single-epoch security definition for the warmup DDH → CKA reduction.

This file packages the single-epoch game from `CKA/SecurityGame.lean`. It is
useful for the warmup reduction layer, but it is not the paper-faithful
Definition 13 surface; that lives in `CKA/Figure3Game.lean`.
-/

set_option autoImplicit false

namespace CKA

variable {SharedKey SenderState ReceiverState Msg Output : Type}

/-- Auxiliary single-epoch `ε`-security predicate for the warmup game. -/
def CKASecure [SampleableType SharedKey] [SampleableType Output]
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (ε : ℝ) : Prop :=
  ∀ adversary : CKAAdversary Msg Output,
    ckaDistAdvantage cka adversary ≤ ε

end CKA
