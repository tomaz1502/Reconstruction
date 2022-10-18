import Meta.Boolean
import Meta.Resolution
import Lean

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Expr
open Lean.Meta

def congDupOr (i : Nat) (nm : Ident) (last : Bool) : TacticM Syntax :=
  match i with
  | 0 =>
    if last then `(dupOr₂ $nm)
    else `(dupOr $nm)
  | (i' + 1) => do
    let nm' := mkIdent (Name.mkSimple "w")
    let r ← congDupOr i' nm' last
    let r: Term := ⟨r⟩
    `(congOrLeft (fun $nm' => $r) $nm)

-- i: the index fixed in the original list
-- j: the index of li.head! in the original list
def loop (i j n : Nat) (pivot : Expr) (li : List Expr) (nm : Ident) : TacticM Ident :=
  match li with
  | [] => return nm
  | e::es =>
    if e == pivot then do
      -- step₁: move expr that is equal to the pivot to position i + 1
      let step₁ ←
        if j > i + 1 then
          let fname ← mkIdent <$> mkFreshId
          let e ← getExprInContext nm.getId
          let t ← instantiateMVars e
          pullIndex2 (i + 1) j nm t fname
          pure fname
        else pure nm

      -- step₂: apply congOrLeft i times with dupOr
      let step₂: Ident ← do
        let last := i + 1 == n - 1
        let tactic ← congDupOr i step₁ last 
        let tactic := ⟨tactic⟩
        let fname ← mkIdent <$> mkFreshId
        evalTactic (← `(tactic| have $fname := $tactic))
        pure fname

      loop i j (n - 1) pivot es step₂
    else loop i (j + 1) n pivot es nm

def factorCore (type : Expr) (source result : Ident) : TacticM Unit :=
  withMainContext do
    let mut li := collectPropsInOrChain type
    let n := li.length
    let mut answer := source
    for i in List.range n do
      li := List.drop i li
      match li with
      | [] => break
      | e::es => do
        answer ← loop i (i + 1) (li.length + i) e es answer
        let e ← getExprInContext answer.getId
        let t ← instantiateMVars e
        li := collectPropsInOrChain t

    evalTactic (← `(tactic| have $result := $answer))

syntax (name := factor) "factor" term "," ident : tactic

@[tactic factor] def evalFactor : Tactic := fun stx =>
  withMainContext do
    let e ← elabTerm stx[1] none
    let type ← inferType e
    let source := ⟨stx[1]⟩
    let result := ⟨stx[3]⟩
    factorCore type source result

example : A ∨ A ∨ A ∨ A ∨ B ∨ A ∨ B ∨ A ∨ C ∨ B ∨ C ∨ B ∨ A → True :=
  by intro h
     factor h, bla

     admit
