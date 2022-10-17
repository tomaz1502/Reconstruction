import Meta.Resolution

import Lean
open Lean
open Lean.Elab.Tactic Lean.Syntax Lean.Elab Lean.Expr
open Lean.Elab.Tactic

-- TODO: find a way to remove '?' without breaking the parser
syntax (name := permutateOr) "permutateOr" term "," ("[" term,* "]")? : tactic

def parsePermuteOr : Syntax → TacticM (List Nat)
  | `(tactic| permutateOr $_, [ $[$hs],* ]) => hs.toList.mapM stxToNat
  | _                                      => throwError "ble"

def getIthExpr : Nat → Expr → Option Expr
  | Nat.zero, app (app (const `Or ..) t₁) _ => some t₁
  | Nat.zero, t                             => some t -- last element in or chain
  | i + 1,    app (app (const `Or ..) _) t₂ => getIthExpr i t₂
  | _, _                                    => none

@[tactic permutateOr] def evalPermutateOr : Tactic :=
  fun stx => withMainContext do
    let hyp ← elabTerm stx[1] none
    let type ← instantiateMVars (← Meta.inferType hyp)
    let hs ← parsePermuteOr stx
    let conclusion ← go hs.reverse type hyp stx[1]
    Tactic.closeMainGoal conclusion
where go : List Nat → Expr → Expr → Syntax → TacticM Expr
       | [], _, hyp, _ => return hyp
       | (i::is), type, hyp, stx => do
         let fname ← mkIdent <$> mkFreshId
         let fnameId := fname.getId
         let ithExpr ←
           match getIthExpr i type with
           | some e => pure e
           | none   => throwError "invalid permutation"
         let type ← instantiateMVars (← Meta.inferType hyp)
         pullCore ithExpr type stx fnameId
         withMainContext do
           let ctx ← getLCtx
           let hyp' := (ctx.findFromUserName? fnameId).get!.toExpr
           go is type hyp' stx


example : A ∨ B ∨ C ∨ D ∨ E → True := by
  intro h
  trivial
  /- permutateOr h, [2, 1, 3, 4, 0] -/
  /- trivial -/

