import Meta.Boolean
import Meta.Resolution
import Lean

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Expr
open Lean.Meta

def excludeFirst : Expr → Expr :=
  createOrChain ∘ List.drop 1 ∘ collectPropsInOrChain

def eraseDups : Expr → Expr :=
  createOrChain ∘ List.eraseDups ∘ collectPropsInOrChain

def go (hyp type e : Expr) (li : List Expr) (name : Name) : TacticM Name := do
   match li with
   | []   => return name
   | h::t => match e == h with
             | false => go hyp type e t name
             | true  =>
               withMainContext do
                 let fname ← mkFreshId
                 try
                   pullCore h hyp type fname
                 catch e => do
                   throwError e.toMessageData
                 logInfo m!"HERE: {h} -- {hyp} -- {type}"
                 withMainContext do
                   let fname2 ← mkFreshId
                   let ctx ← getLCtx
                   let pullHyp := (ctx.findFromUserName? (mkIdent fname).getId).get!.toExpr
                   let pullHypType ← inferType pullHyp
                   -- jump the first occurence (the one pulled by pullCore)
                   let index := (getOccs h type).get! 1
                   pullIndex index pullHyp pullHypType fname2
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
                       if getLength newGoal > 2 then
                         evalTactic (← `(tactic| exact dupOr $(mkIdent fname2)))
                       else
                         evalTactic (← `(tactic| exact dupOr₂ $(mkIdent fname2)))
                       withMainContext do
                         let ctx3 ← getLCtx
                         let dupFreeHyp := (ctx3.findFromUserName? (mkIdent fname3).getId).get!.toExpr
                         evalTactic (← `(tactic| clear $(mkIdent fname)))
                         evalTactic (← `(tactic| clear $(mkIdent fname2)))
                         go dupFreeHyp newGoal e t fname3


def factorLoop (hyp type : Expr) (li : List Expr) (name : Name) : TacticM Name :=
  match li with
  | []    => return name
  | e::es =>
    withMainContext do
      let fname ← mkFreshId
      let newName ← go hyp type e es fname
      withMainContext do
        let ctx ← getLCtx
        match (ctx.findFromUserName? (mkIdent newName).getId) with
        | none => factorLoop hyp type es name
        | some newHyp' =>
          let newHyp := newHyp'.toExpr
          let newType ← inferType newHyp
          if Option.isSome (ctx.findFromUserName? name)
          then
            evalTactic (← `(tactic| clear $(mkIdent name)))
          else pure ()
          factorLoop newHyp newType es newName

def factorCore (e type : Expr) (name : Name) : TacticM Unit :=
  withMainContext do
    let li := collectPropsInOrChain type
    let fname ← mkFreshId
    let newName ← factorLoop e type li fname
    let newExpr ←
      withMainContext do
        let ctx ← getLCtx
        match ctx.findFromUserName? (mkIdent newName).getId with
        | none      => pure e
        | some hyp' => pure $ hyp'.toExpr
    let newGoal := eraseDups type
    let mvarId ← getMainGoal
    Meta.withMVarContext mvarId do
      let p ← Meta.mkFreshExprMVar newGoal MetavarKind.syntheticOpaque name
      let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name newGoal p
      replaceMainGoal [p.mvarId!, mvarIdNew]
      Tactic.closeMainGoal newExpr
      evalTactic (← `(tactic| clear $(mkIdent newName)))

syntax (name := factor) "factor" term "," ident : tactic

@[tactic factor] def evalFactor : Tactic := fun stx =>
  withMainContext do
    let e ← elabTerm stx[1] none
    let type ← inferType e
    let name := Syntax.getId stx[3]
    factorCore e type name

example : A ∨ A ∨ A → True :=
  by intro h
     /- factor h, bla -/

     admit
