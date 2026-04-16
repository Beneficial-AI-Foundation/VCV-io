import Lean.Elab.Tactic

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic.TacticInternals

/-- Detect whether an expression is `Sum α β` (after whnf). -/
private def isSumType (e : Expr) : MetaM Bool := do
  let e ← whnf e
  return e.isAppOfArity ``Sum 2

/-- Recursively case-split a hypothesis whose type is a nested `Sum`. At each level,
runs `cases t`, which produces `.inl` and `.inr` goals. Then recurses on the `.inl`
goal if its rebound variable is still a `Sum`. -/
private partial def casesOracleCore (t : TSyntax `ident) : TacticM Unit :=
  withMainContext do
    let fvarId ← getFVarId t
    let ty ← instantiateMVars (← fvarId.getType)
    let isSumTy ← isSumType ty
    if !isSumTy then return
    evalTactic (← `(tactic| cases $t:ident with | inl $t => ?_ | inr $t => ?_))
    let allGoals ← getGoals
    if allGoals.isEmpty then return
    let inlGoal := allGoals.head!
    let rest := allGoals.tail!
    setGoals [inlGoal]
    casesOracleCore t
    let inlGoals ← getGoals
    setGoals (inlGoals ++ rest)

end OracleComp.ProgramLogic.TacticInternals

/-- `cases_oracle t` performs a complete case split on a variable `t` whose type
is a nested `Sum` (as arises from `OracleSpec` addition). It produces one subgoal
per summand (i.e. per oracle in the composed spec).

Example: if `t : ((α ⊕ β) ⊕ γ) ⊕ δ`, then `cases_oracle t` produces four subgoals
with `t` specialized to each leaf type. -/
syntax "cases_oracle" ident : tactic

elab_rules : tactic
  | `(tactic| cases_oracle $t:ident) =>
    withMainContext do
      let fvarId ← getFVarId t
      let ty ← instantiateMVars (← fvarId.getType)
      let isSumTy ← OracleComp.ProgramLogic.TacticInternals.isSumType ty
      if !isSumTy then
        throwError "cases_oracle: type of '{t}' is not a Sum type"
      OracleComp.ProgramLogic.TacticInternals.casesOracleCore t
