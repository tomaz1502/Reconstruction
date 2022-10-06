import Meta.Boolean
import Lean

open Lean
open Lean.Elab.Tactic
open Lean.Expr

def traverseAux (seen : List Expr) (tl : List Expr) : TacticM Unit :=
  sorry

def traverse (e : Expr) : TacticM Unit :=
  let li := collectPropsInOrChain e
  -- First just remove duplicates without caring about the
  -- order. Later we label each prop and use permutateOr
  -- to fix the order
  traverseAux [] li

syntax (name := factor) "factor" term "," term : tactic

@[tactic factor] def evalFactor : Tactic := fun stx =>
  withMainContext do
    sorry
