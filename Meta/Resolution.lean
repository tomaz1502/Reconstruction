import Meta.Boolean

import Lean

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta
open List Expr

-- assuming `o` to be an OrChain, returns how many Props are
-- to the left of `t`
def getIndex (t o : Expr) : Option Nat :=
  match o with
  | app (app (const `Or ..) e1) e2 => if e1 == t then some 0
                                      else (. + 1) <$> getIndex t e2
  | e => if e == t then some 0
         else none

def applyList (l: List Term) (res: Term) : TacticM Term :=
  match l with
  | [] => return res
  | t::ts =>
    withMainContext do
      let res' := Syntax.mkApp t #[res]
      let fname ← mkIdent <$> mkFreshId
      evalTactic (← `(tactic| have $fname := $res'))
      applyList ts fname

def fold (l : List Term) (nm : Ident) : Syntax :=
  match l with
  | [] => nm
  | t::ts =>
    let rest := fold ts nm
    let rest := ⟨rest⟩
    Syntax.mkApp t #[rest]

def go (tactics : List Term) (i : Nat) (nm : Ident) (last : Bool) : TacticM Syntax :=
  match i with
  | 0 =>
    withMainContext do
      if last then
        let innerProof := fold tactics nm
        let innerProof: Term := ⟨innerProof⟩
        `($innerProof)
      else
        let fname := mkIdent (Name.mkSimple "w")
        let innerProof := fold tactics fname
        let innerProof: Term := ⟨innerProof⟩
        `(congOrRight (fun $fname => $innerProof) $nm)
  | (i' + 1) =>
    withMainContext do
      let nm' := Name.mkSimple "w"
      let nm' := mkIdent nm'
      let r ← go tactics i' nm' last
      let r: Term := ⟨r⟩
      `(congOrLeft (fun $nm' => $r) $nm)

-- pull j-th term in the orchain to i-th position (we start counting indices at 0)
-- TODO: clear intermediate steps
def pullIndex2 (i j : Nat) (hyp : Syntax) (type : Expr) (name : Name) : TacticM Unit :=
  if i == j then do
    let hyp: Term := ⟨hyp⟩
    evalTactic (← `(tactic| have $(mkIdent name) := $hyp))
  else withMainContext do
    let last := getLength type == j + 1
    let step₁: Ident ← 
      if last then pure ⟨hyp⟩
      else do
        let v := List.take (j - i) $ getCongAssoc j `orAssocDir
        let res: Term := ⟨hyp⟩
        let step₁: Term ← applyList v res
        let step₁: Ident := ⟨step₁⟩ 
        pure step₁ 

    let step₂: Ident ←
      if last then do
        let tactics := List.take (j - 1 - i) $ getCongAssoc (j - 1) `orAssocDir
        let step₂: Term ← applyList tactics step₁
        let step₂: Ident := ⟨step₂⟩
        pure step₂
      else do
        let tactics₂ := List.reverse $ getCongAssoc (j - i - 1) `orAssocDir
        let wrappedTactics₂: Syntax ← go tactics₂ i step₁ last
        let wrappedTactics₂: Term := ⟨wrappedTactics₂⟩
        let fname₂ ← mkIdent <$> mkFreshId
        evalTactic (← `(tactic| have $fname₂ := $wrappedTactics₂))
        pure fname₂
    
    let orComm: Term := ⟨mkIdent `orComm⟩
    let wrappedTactics₃ ← go [orComm] i step₂ last
    let wrappedTactics₃ := ⟨wrappedTactics₃⟩
    let step₃ ← mkIdent <$> mkFreshId
    evalTactic (← `(tactic| have $step₃ := $wrappedTactics₃))

    let step₄: Ident ←
      if last then do pure step₃ 
      else do
        let u := List.reverse $ List.take (j - i) $ getCongAssoc j `orAssocConv
        let step₄: Term ← applyList u step₃
        let step₄: Ident := ⟨step₄⟩
        pure step₄

    evalTactic (← `(tactic| have $(mkIdent name) := $step₄))

syntax (name := pull2) "pull2" term "," term "," term "," ident : tactic

@[tactic pull2] def evalPull2 : Tactic := fun stx => withMainContext do
  let i ← stxToNat ⟨stx[1]⟩ 
  let j ← stxToNat ⟨stx[3]⟩
  let nm := stx[7].getId
  let e ← elabTerm stx[5] none
  let t ← instantiateMVars (← Meta.inferType e)
  pullIndex2 i j stx[5] t nm

def pullIndex (index : Nat) (hypS : Syntax) (type : Expr) (name : Name) : TacticM Unit :=
  pullIndex2 0 index hypS type name

-- insert pivot in the first position of the or-chain
-- represented by hyp
def pullCore (pivot type : Expr) (hypS : Syntax) (name : Name) : TacticM Unit := do
  let index' := getIndex pivot type
  let index ←
    match index' with
    | some i => pure i
    | none   => throwError "term not found"
  pullIndex index hypS type name

example : A ∨ B ∨ C ∨ D → True := by
  intro h
  pull2 0, 3, h, bla

  exact True.intro

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
  let pivotExpr     ← elabTerm pivotTerm none
  let notPivotExpr  ← elabTerm notPivot none
  let firstHypType  ← inferType (← elabTerm firstHyp none)
  let secondHypType ← inferType (← elabTerm secondHyp none)

  let lenGoal ← getLength <$> getMainTarget
  pullCore pivotExpr    firstHypType  firstHyp  fname1
  pullCore notPivotExpr secondHypType secondHyp fname2

  let fident1 := mkIdent fname1
  let fident2 := mkIdent fname2
  let len₁ := getLength firstHypType
  let len₂ := getLength secondHypType

  if lenGoal > 2 then
    for s in getCongAssoc (len₁ - 2) `orAssocConv do
      evalTactic (← `(tactic| apply $s))
      logInfo m!"....apply {s}"
      printGoal

  if len₁ > 1 then
    if len₂ > 1 then
      evalTactic (← `(tactic| exact resolution_thm $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm"
    else
      evalTactic (← `(tactic| exact resolution_thm₃ $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm₃"
  else
    if len₂ > 1 then
      evalTactic (← `(tactic| exact resolution_thm₂ $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm₂"
    else
      evalTactic (← `(tactic| exact resolution_thm₄ $fident1 $fident2))
      logInfo m!"..close goal with resolution_thm₄"

syntax (name := resolution_1) "R1" ident "," ident "," term : tactic
@[tactic resolution_1] def evalResolution_1 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    resolutionCore firstHyp secondHyp pivotTerm

syntax (name := resolution_2) "R2" ident "," ident "," term : tactic
@[tactic resolution_2] def evalResolution_2 : Tactic :=
  fun stx => withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    resolutionCore secondHyp firstHyp pivotTerm

