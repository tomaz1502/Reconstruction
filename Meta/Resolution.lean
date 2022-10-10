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

def eliminateIndex (i : Nat) (e : Expr) : Expr :=
  match e with
  | app (app (const `Or ..) e1) e2 =>
    match i with
    | 0 => e2
    | 1 => match e2 with
           | app (app (const `Or ..) _) e3 => mkApp (mkApp (mkConst `Or) e1) e3
           | _ => e1
    | i' =>
        mkApp (mkApp (mkConst `Or) e1) $ eliminateIndex (i' - 1) e2
  | e => e

-- assuming `o` to be an OrChain, returns how many Props are
-- to the left of `t`
def getIndex (t o : Expr) : Option Nat :=
  match o with
  | app (app (const `Or ..) e1) e2 => if e1 == t then some 0
                                      else (. + 1) <$> getIndex t e2
  | e => if e == t then some 0
         else none

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

def pullGoal (i : Nat) (o : Expr) : Expr :=
  match o with
  | app (app (const `Or ..) _) _ =>
    let rest    := eliminateIndex i o
    let ithExpr := (collectPropsInOrChain o).get! i
    mkApp (mkApp (mkConst `Or) ithExpr) rest
  -- if `o` is a single expression then we're assuming
  -- it is equals to `t` useful for corner cases (resolution
  -- that results in empty clause)
  | e => e

def pull2Goal (i : Nat) (o : Expr) : Expr :=
  match o with
  | app (app (const `Or ..) e₁) _ =>
    let rest    := eliminateIndex i o
    let ithExpr := (collectPropsInOrChain o).get! i
    mkApp (mkApp (mkConst `Or) e₁) (mkApp (mkApp (mkConst `Or) ithExpr) rest)
  | _ => o

/- def pull2Goal (t o : Expr) : Expr := -/
/-   match o with -/
/-   | app (app (const `Or ..) e₁) e₂ => -/ 
                                /-     let rest := eliminate t e₂ -/
/-     mkApp (mkApp (mkConst `Or) e₁) (mkApp (mkApp (mkConst `Or) t) rest) -/
/-   | _ => o -/

def pullIndex (index : Nat) (hyp type : Expr) (name : Name) : TacticM Unit :=
  withMainContext do
    let l := getLength type
    let arr : List Term :=
      if index = 0 then []
      else if l = index + 1 then tacticsLastIndex index
           else tacticsRegular index
    let newGoal := pullGoal index type
    let mvarId ← getMainGoal
    Meta.withMVarContext mvarId do
      let p ← Meta.mkFreshExprMVar newGoal MetavarKind.syntheticOpaque name
      let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name newGoal p
      replaceMainGoal [p.mvarId!, mvarIdNew]
      for s in arr do
        evalTactic (← `(tactic| apply $s))
      Tactic.closeMainGoal hyp

-- insert pivot in the first position of the or-chain
-- represented by hyp
def pullCore (pivot hyp : Expr) (name : Name) : TacticM Unit :=
  withMainContext do
    let type ← Meta.inferType hyp
    let index' := getIndex pivot type
    let index ←
      match index' with
      | some i => pure i
      | none   => throwError "term not found"
    pullIndex index hyp type name

syntax (name := pull) "pull" term "," term "," ident : tactic

@[tactic pull] def evalPull : Tactic := fun stx => withMainContext do
  let pivot ← elabTerm stx[1] none
  let hyp ← elabTerm stx[3] none
  let name := stx[5].getId
  pullCore pivot hyp name     

example : A ∨ B ∨ C ∨ D → True := by
  intro h
  pull C, h, ble
  pull D, ble, bli

  admit

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

def resolutionCore (firstHyp secondHyp : Ident) (pivotTerm : Term) : TacticM Unit := do
  let fname1 ← mkFreshId
  let fname2 ← mkFreshId
  let notPivot : Term := Syntax.mkApp (mkIdent `Not) #[pivotTerm]
  let pivotExpr ← elabTerm pivotTerm none
  let notPivotExpr ← elabTerm notPivot none
  let firstHypExpr ← elabTerm firstHyp none
  let secondHypExpr ← elabTerm secondHyp none
  pullCore pivotExpr    firstHypExpr  fname1
  pullCore notPivotExpr secondHypExpr fname2
  -- I dont know why but the context doesn't automatically refresh to include the new hypothesis
  -- thats why we have another `withMainContext` here
  withMainContext do
    let ctx ← getLCtx
    let fident1 := mkIdent fname1
    let fident2 := mkIdent fname2
    let reordFirstHyp ← inferType (ctx.findFromUserName? fident1.getId).get!.toExpr
    let reordSecondHyp ← inferType (ctx.findFromUserName? fident2.getId).get!.toExpr
    let len₁ := getLength reordFirstHyp
    let len₂ := getLength reordSecondHyp
    let lenGoal ← getLength <$> getMainTarget

    -- TODO: understand why this if's is necessary
    if lenGoal > 2 then
      for s in getCongAssoc (len₁ - 2) `orAssocConv do
        evalTactic (← `(tactic| apply $s))
        logInfo m!"....apply {s}"
        printGoal

    if len₁ > 1 then
      if len₂ > 1 then
        /- Tactic.closeMainGoal (mkApp (mkApp (mkConst `resolution_thm) bla) ble) -/
        evalTactic (← `(tactic| exact resolution_thm $fident1 $fident2))
        logInfo m!"..close goal with resolution_thm"
      else
        /- Tactic.closeMainGoal (mkApp (mkApp (mkConst `resolution_thm₃) bla) ble) -/
        evalTactic (← `(tactic| exact resolution_thm₃ $fident1 $fident2))
        logInfo m!"..close goal with resolution_thm₃"
    else
      if len₂ > 1 then
        /- Tactic.closeMainGoal (mkApp (mkApp (mkConst `resolution_thm₂) bla) ble) -/
        evalTactic (← `(tactic| exact resolution_thm₂ $fident1 $fident2))
        logInfo m!"..close goal with resolution_thm₂"
      else
        /- Tactic.closeMainGoal (mkApp (mkApp (mkConst `resolution_thm₄) bla) ble) -/
        evalTactic (← `(tactic| exact resolution_thm₄ $fident1 $fident2))
        logInfo m!"..close goal with resolution_thm₄"
  

syntax (name := resolution_1) "resolution_1" ident "," ident "," term : tactic

@[tactic resolution_1] def evalResolution_1 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨ stx[1] ⟩
    let secondHyp : Ident := ⟨ stx[3] ⟩
    let pivotTerm : Term := ⟨ stx[5] ⟩
    resolutionCore firstHyp secondHyp pivotTerm

syntax (name := resolution_2) "resolution_2" ident "," ident "," term : tactic

@[tactic resolution_2] def evalResolution_2 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨ stx[1] ⟩
    let secondHyp : Ident := ⟨ stx[3] ⟩
    let pivotTerm : Term := ⟨ stx[5] ⟩
    resolutionCore secondHyp firstHyp pivotTerm

