import Meta.Boolean
import Meta.Resolution
import Lean

open Lean
open Lean.Elab.Tactic
open Lean.Expr
open Lean.Meta
open Lean.Elab

def excludeFirst : Expr → Expr :=
  createOrChain ∘ List.drop 1 ∘ collectPropsInOrChain

def go (hyp e : Expr) (li : List Expr) (name : Name) : TacticM Name :=
  match li with
  | []   => return name
  | h::t => match e == h with
            | true  =>
              withMainContext do
                let fname ← mkFreshId
                pullCore h hyp fname
                withMainContext do
                  let fname2 ← mkFreshId
                  let ctx ← getLCtx
                  let pullHyp ← inferType (ctx.findFromUserName? (mkIdent fname).getId).get!.toExpr
                  -- jump the first occurence (the one pulled by pullCore)
                  let index := (getOccs h hyp).get! 1
                  pull2Index index pullHyp fname2
                  withMainContext do
                    let ctx2 ← getLCtx
                    let pull2Hyp ← inferType (ctx2.findFromUserName? (mkIdent fname2).getId).get!.toExpr
                    let fname3 ← mkFreshId
                    let newGoal := excludeFirst pull2Hyp                   
                    let mvarId ← getMainGoal
                    Meta.withMVarContext mvarId do
                      let p ← Meta.mkFreshExprMVar newGoal MetavarKind.syntheticOpaque fname3
                      let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId fname3 newGoal p
                      replaceMainGoal [p.mvarId!, mvarIdNew]
                      Tactic.closeMainGoal (mkApp (mkConst `dupOr) pull2Hyp)
                      withMainContext do
                        let ctx3 ← getLCtx
                        let dupFreeHyp ← inferType (ctx3.findFromUserName? (mkIdent fname3).getId).get!.toExpr
                        go dupFreeHyp e t fname3
            | false => go hyp e t name

def factorCore (e : Expr) (name : Name) : TacticM Unit :=
  withMainContext do
    return ()

syntax (name := factor) "factor" term "," term : tactic

@[tactic factor] def evalFactor : Tactic := fun stx =>
  withMainContext do
    sorry
