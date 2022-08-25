import Lean

open Lean Lean.Expr Lean.Meta

variable {n m : Nat} 

example : n = m :=
  by apply Eq.trans
     -- n = ?b
     -- ?b = m
     sorry
     sorry
     sorry



#check @Eq.trans Nat n m

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

#check mkFreshExprMVar

#check getLCtx

#check instantiateMVars

def someNumber : Nat := (. + 2) $ 3

#eval someNumber

#eval mkConst ``someNumber

#eval reduce (mkConst ``someNumber)

#reduce someNumber

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  checkNotAssigned mvarId `myAssumption
  withMVarContext mvarId do
    let target ← getMVarType mvarId
    for ldecl in ← getLCtx do
      if ldecl.isAuxDecl then
        continue
      if ← isDefEq ldecl.type target then
        assignExprMVar mvarId ldecl.toExpr
        return true
    return false



syntax "custom_tactic" : tactic

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

example : 43 = 43 ∧ 42 = 42 := by
  custom_tactic


elab "custom_assump_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType goalType
        then return Option.some declExpr
        else return Option.none
    match option_matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal e
    | none => Lean.Meta.throwTacticEx `custom_assump_2 goal
                (m!"unable to find matching hypothesis of type ({goalType})")

example (H1 : 1 = 1) (H2 : 2 = 2)  : 2 = 2 := by
  custom_assump_2

example (H1 : 1 = 1)  : 2 = 2 := by
  custom_assump_2

