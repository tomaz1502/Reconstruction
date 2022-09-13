import Meta.Boolean

import Lean

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta
open List Expr

-- eliminates first occurence of `e` in `o`
def eliminate (e o : Expr) : Expr :=
  match o with
  | app s@(app (const `Or ..) e1) e2 =>
    if e1 == e then e2 else
      if e2 == e then e1 else
        app s (eliminate e e2)
  | e => e

-- assuming `o` to be an OrChain, returns how many Props are
-- to the left of `t`
def getIndex (t o : Expr) : Option Nat :=
  match o with
  | app (app (const `Or ..) e1) e2 => if e1 == t then some 0
                                      else (. + 1) <$> getIndex t e2
  | e => if e == t then some 0
         else none

def getLength (o : Expr) : Nat :=
  match o with
  | app (app (const `Or ..) _) e2 => 1 + getLength e2
  | _ => 1

def getCongAssoc' : Nat → Name → Term
| 0,     n => mkIdent n
| i + 1, n => Syntax.mkApp (mkIdent `congOrLeft) #[getCongAssoc' i n]

def getCongAssoc : Nat → Name → List Term
| 0,     _ => []
| 1,     n => [getCongAssoc' 0 n]
| i + 2, n => (getCongAssoc' (i + 1) n) :: (getCongAssoc (i + 1) n)

def tacticsLastIndex (index : Nat) : List Term :=
  (mkIdent `orComm) :: reverse (getCongAssoc (index - 1) `orAssocDir)

def tacticsRegular (index : Nat) : List Term :=
  let tactics₁ := getCongAssoc index `orAssocConv
  let tactics₂ := [ Syntax.mkApp (mkIdent `congOrRight) #[mkIdent `orComm] ]
  let tactics₃ := reverse $
    map (λ e => Syntax.mkApp (mkIdent `congOrRight) #[e])
      (getCongAssoc (index - 1) `orAssocDir)
  let tactics₄ := reverse (getCongAssoc index `orAssocDir)
  tactics₁ ++ tactics₂ ++ tactics₃ ++ tactics₄

-- defines the expr corresponding to the goal of reorder,
-- assuming we want to pull `t` in `o`
def reorderGoal (t o : Expr) : Expr :=
  match o with
  | app (app (const `Or ..) _) _ => app (app (mkConst `Or) t) (eliminate t o)
  -- if `o` is a single expression then we're assuming it is equals to `t`
  -- useful for corner cases (resolution that results in empty clause)
  | _ => t

syntax (name := reorder) "reorder" term "," ident "," ident : tactic

@[tactic reorder] def evalReorder : Tactic := fun stx => withMainContext do
  let pivot ← elabTerm stx[1] none
  let hyp ← elabTerm stx[3] none
  let type ← Meta.inferType hyp
  let index' := getIndex pivot type
  let index ←
    match index' with
    | some i => pure i
    | none   => throwError "term not found"

  logInfo m!"Reorder {type} for pivot {pivot} (pos {index})"
  let l := getLength type
  let arr : List Term :=
    if index = 0 then []
    else if l = index + 1 then tacticsLastIndex index
         else tacticsRegular index

  let new_term := reorderGoal pivot type
  logInfo m!"..expected goal is {new_term}"
  let mvarId ← getMainGoal
  Meta.withMVarContext mvarId do
    let name := stx[5].getId
    let p ← Meta.mkFreshExprMVar new_term MetavarKind.syntheticOpaque name
    let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name new_term p
    replaceMainGoal [p.mvarId!, mvarIdNew]
    let printGoal : TacticM Unit := do
      let currGoal ← getMainGoal
      let currGoalType ← getMVarType currGoal
      logInfo m!"......new goal: {← instantiateMVars currGoalType}"
    for s in arr do
      logInfo m!"....apply {s}"
      evalTactic (← `(tactic| apply $s))
      printGoal
    logInfo m!"..close goal\n"
    Tactic.closeMainGoal hyp

theorem resolution_thm : ∀ {A B C : Prop}, (A ∨ B) → (¬ A ∨ C) → B ∨ C := by
  intros A B C h₁ h₂
  cases h₁ with
  | inl ap => cases h₂ with
              | inl nap => exact (False.elim (nap ap))
              | inr cp  => exact (Or.inr cp)
  | inr bp => exact (Or.inl bp)

theorem resolution_thm₂ : ∀ {A C: Prop}, A → (¬ A ∨ C) → C := λ a ornac =>
  match ornac with
  | Or.inl na => False.elim (na a)
  | Or.inr c  => c

theorem resolution_thm₃ : ∀ {A B: Prop}, (A ∨ B) → ¬ A → B := λ orab na =>
  match orab with
  | Or.inl a => False.elim (na a)
  | Or.inr b => b

theorem resolution_thm₄ : ∀ {A : Prop}, A → ¬ A → False := λ a na => na a

-- maybe extract another function and refactor (eliminate (mkNot r) o₂)
def get_resolution_goal (o₁ o₂ r : Expr) : Expr :=
  match o₁ with
  | app s@(app (const `Or ..) e₁) e₂ =>
    if e₁ == r then get_resolution_goal e₂ o₂ r -- TODO: this is a wrong, if we have multiple ocurrences of r in o₁
    else app s (get_resolution_goal e₂ o₂ r)
  | e =>
    if e == r then
      if o₂ == mkNot r then mkConst `False else eliminate (mkNot r) o₂
    else if o₂ == mkNot r then
      e else app (app (const `Or []) e) (eliminate (mkNot r) o₂)

syntax (name := resolution) "resolution" ident "," ident "," term "," ident : tactic

@[tactic resolution] def evalResolution : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨ stx[1] ⟩
    let secondHyp : Ident := ⟨ stx[3] ⟩
    let fname1 ← mkIdent <$> mkFreshId
    let fname2 ← mkIdent <$> mkFreshId
    let pivotTerm : Term := ⟨ stx[5] ⟩
    let notPivot : Term := Syntax.mkApp (mkIdent `Not) #[pivotTerm]

    evalTactic  (← `(tactic| reorder $pivotTerm, $firstHyp, $fname1))
    evalTactic  (← `(tactic| reorder $notPivot, $secondHyp, $fname2))

    -- I dont know why but the context doesn't automatically refresh to include the new hypothesis
    -- thats why we have another `withMainContext` here
    withMainContext do
      let ctx ← getLCtx
      let reordFirstHyp ← inferType (ctx.findFromUserName? fname1.getId).get!.toExpr
      let reordSecondHyp ← inferType (ctx.findFromUserName? fname2.getId).get!.toExpr

      let pivot ← elabTerm stx[5] none
      let resolvant := get_resolution_goal reordFirstHyp reordSecondHyp pivot
      let mvarId ← getMainGoal
      logInfo m!"Resolve [{pivot}]: {reordFirstHyp} <> {reordSecondHyp}"
      logInfo m!"..expected goal: {← getMVarType mvarId}"
      Meta.withMVarContext mvarId do
        let name := stx[7].getId
        let p ← Meta.mkFreshExprMVar resolvant MetavarKind.syntheticOpaque name
        let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name resolvant p
        replaceMainGoal [p.mvarId!, mvarIdNew]
        let len₁ := getLength reordFirstHyp
        let len₂ := getLength reordSecondHyp
        -- parenthesize preffix in goal corresponding to first hyp
        let printGoal : TacticM Unit := do
          let currGoal ← getMainGoal
          let currGoalType ← getMVarType currGoal
          logInfo m!"......new goal: {← instantiateMVars currGoalType}"
        for s in getCongAssoc (len₁ - 2) `orAssocConv do
          evalTactic (← `(tactic| apply $s))
          logInfo m!"....apply {s}"
          printGoal

        if len₁ > 1 then
          if len₂ > 1 then
            evalTactic (← `(tactic| exact resolution_thm $fname1 $fname2))
            logInfo m!"..close goal with resolution_thm"
          else
            evalTactic (← `(tactic| exact resolution_thm₃ $fname1 $fname2))
            logInfo m!"..close goal with resolution_thm₃"
        else
          if len₂ > 1 then
            evalTactic (← `(tactic| exact resolution_thm₂ $fname1 $fname2))
            logInfo m!"..close goal with resolution_thm₂"
          else
            evalTactic (← `(tactic| exact resolution_thm₄ $fname1 $fname2))
            logInfo m!"..close goal with resolution_thm₄"

        evalTactic (← `(tactic| clear $fname1 $fname2))

-- example usage:
example : A ∨ B ∨ C ∨ D → E ∨ F ∨ ¬ B ∨ G → A ∨ C ∨ D ∨ E ∨ F ∨ G := by
  intros h₁ h₂
  resolution h₁, h₂, B, h₃

  have b₁ : B := sorry
  have b₂ : ¬ B := sorry

  /- have b₃ := resolution_thm₃ b₁ b₂ -/ 

  resolution b₁, b₂, B, b₃

  exact h₃
