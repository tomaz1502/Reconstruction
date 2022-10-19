import Lean

import Meta.Boolean

open Lean Elab Tactic

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
  | 0 => do
    if last then
      let innerProof := fold tactics nm
      let innerProof: Term := ⟨innerProof⟩
      `($innerProof)
    else
      let nm' := mkIdent (Name.mkSimple "w")
      let innerProof := fold tactics nm'
      let innerProof: Term := ⟨innerProof⟩
      `(congOrRight (fun $nm' => $innerProof) $nm)
  | (i' + 1) => do
    let nm' := mkIdent (Name.mkSimple "w")
    let r ← go tactics i' nm' last
    let r: Term := ⟨r⟩
    `(congOrLeft (fun $nm' => $r) $nm)

-- pull j-th term in the orchain to i-th position (we start counting indices at 0)
-- TODO: clear intermediate steps
def pullIndex2 (i j : Nat) (hyp : Syntax) (type : Expr) (id : Ident) : TacticM Unit :=
  if i == j then do
    let hyp: Term := ⟨hyp⟩
    evalTactic (← `(tactic| have $id := $hyp))
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

    evalTactic (← `(tactic| have $id := $step₄))

syntax (name := pull2) "pull2" term "," term "," term "," ident : tactic

@[tactic pull2] def evalPull2 : Tactic := fun stx => withMainContext do
  let i ← stxToNat ⟨stx[1]⟩ 
  let j ← stxToNat ⟨stx[3]⟩
  let id: Ident := ⟨stx[7]⟩
  let e ← elabTerm stx[5] none
  let t ← instantiateMVars (← Meta.inferType e)
  pullIndex2 i j stx[5] t id

def pullIndex (index : Nat) (hypS : Syntax) (type : Expr) (id : Ident) : TacticM Unit :=
  pullIndex2 0 index hypS type id

-- insert pivot in the first position of the or-chain
-- represented by hyp
def pullCore (pivot type : Expr) (hypS : Syntax) (id : Ident) : TacticM Unit := do
  let index' := getIndex pivot type
  let index ←
    match index' with
    | some i => pure i
    | none   => throwError ("term not found: " ++ (toString pivot))
  pullIndex index hypS type id
