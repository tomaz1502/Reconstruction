import Lean

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta Expr Classical
open Lean.Elab.Term

def andN : List Prop → Prop := λ l =>
  match l with
  | [] => True
  | h :: [] => h
  | h :: t  => h ∧ andN t
 
def orN : List Prop → Prop := λ l =>
  match l with
  | [] => False
  | h :: [] => h
  | h₁ :: h₂ :: t  => h₁ ∨ orN (h₂ :: t)
 
def notList : List Prop → List Prop :=
  List.map Not

theorem orComm : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P := by
  intros P Q h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem orAssocDir : ∀ {P Q R: Prop}, P ∨ Q ∨ R → (P ∨ Q) ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => exact Or.inl (Or.inl h₁)
  | inr h₂ => cases h₂ with
              | inl h₃ => exact Or.inl (Or.inr h₃)
              | inr h₄ => exact Or.inr h₄

theorem orAssocConv : ∀ {P Q R : Prop}, (P ∨ Q) ∨ R → P ∨ Q ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => cases h₁ with
              | inl h₃ => exact Or.inl h₃
              | inr h₄ => exact (Or.inr (Or.inl h₄))
  | inr h₂ => exact Or.inr (Or.inr h₂)

theorem congOrRight : ∀ {P Q R : Prop}, (P → Q) → P ∨ R → Q ∨ R := by
  intros P Q R h₁ h₂
  cases h₂ with
  | inl h₃ => exact Or.inl (h₁ h₃)
  | inr h₄ => exact Or.inr h₄

theorem congOrLeft : ∀ {R P Q : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem orImplies₂ : ∀ {p q : Prop}, (¬ p) ∨ q → p → q := sorry
 
theorem orImplies₃ : ∀ {p q : Prop}, p ∨ q → ¬ p → q := sorry

theorem scope : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q :=
  by intros p q h
     exact match em p with
     | Or.inl pp => match em q with
                    | Or.inl pq => Or.inr pq
                    | Or.inr npq => False.elim (npq (h pp))
     | Or.inr npp => Or.inl npp
 
def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q := scope
 
theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match em p, em q with
     | Or.inl pp,  Or.inl _   => False.elim (h (Or.inl pp))
     | Or.inl pp,  Or.inr _   => False.elim (h (Or.inl pp))
     | Or.inr _,   Or.inl pq  => False.elim (h (Or.inr pq))
     | Or.inr npp, Or.inr npq => And.intro npp npq
 
theorem deMorganSmall₂ : ∀ {p q : Prop}, ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
  by intros p q h
     have ⟨np, nq⟩ := h
     exact match em p, em q with
     | Or.inl pp,  _   => False.elim (np pp) 
     | _        ,  Or.inl pq  => False.elim (nq pq)
     | Or.inr npp, Or.inr npq => λ h₂ =>
                                    match h₂ with
                                    | Or.inl pp => False.elim (npp pp) 
                                    | Or.inr pq => False.elim (npq pq)

theorem doubleNeg : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem doubleNeg₂ : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p
 
theorem deMorgan : ∀ {l : List Prop}, ¬ orN (notList l) → andN l := 
  by intros l h
     exact match l with
     | []   => True.intro
     | [t]  => by simp [andN]
                  simp [notList, orN, List.map] at h
                  cases em t with
                  | inl tt  => exact tt
                  | inr ntt => exact False.elim (h ntt)
     | h₁::h₂::t => by simp [orN, notList, List.map] at h
                       have ⟨ t₁, t₂ ⟩ := deMorganSmall h
                       simp [orN] at t₂
                       have ih := @deMorgan (h₂::t) t₂
                       simp [andN]
                       have t₁' := doubleNeg t₁
                       exact ⟨ t₁', ih ⟩
 
theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notList l) :=
  by intros l h
     exact match l with
     | [] => by simp [orN, notList]
     | [t] => by simp [orN, notList]; simp [andN] at h; exact doubleNeg₂ h
     | h₁::h₂::t => by simp [orN, notList, List.map]
                       simp [andN] at h
                       apply deMorganSmall₂
                       have nnh₁ := doubleNeg₂ (And.left h)
                       have ih := @deMorgan₂ (h₂::t) (And.right h)
                       exact ⟨nnh₁, ih⟩

theorem cnfAndNeg : ∀ (l : List Prop), andN l ∨ orN (notList l) :=
  by intro l
     apply orComm
     apply orImplies
     intro h
     exact deMorgan h
 
theorem cong : ∀ {A B : Type u} {f₁ f₂ : A → B} {t₁ t₂ : A},
  f₁ = f₂ → t₁ = t₂ → f₁ t₁ = f₂ t₂ :=
  by intros A B f₁ f₂ t₁ t₂ h₁ h₂
     rewrite [h₁, h₂]
     exact rfl


def notExpr : Expr → Expr
| app (const `Not ..) e => e
| e => mkApp (mkConst `Not) e

-- TODO: use this style of pattern matching everywhere
def collectNOrNegArgs : Expr → Nat → List Expr
| app (app (const `Or ..) e) _,  1       => [notExpr e]
| app (app (const `Or ..) e1) e2, n + 1 => (notExpr e1) :: collectNOrNegArgs e2 n
| e, _ => [e]

def dropNArgs : Expr → Nat → Expr
| app (app (const `Or ..) _) e2, 1 => e2
| app (app (const `Or ..) _) e2, n + 1 => dropNArgs e2 n
| e, _ => e

def andNE : List Expr → Expr
| [] => mkConst `True
| h :: [] => h
| h :: t => app (app (const `And []) h) (andNE t)

def liftNOrToImpGoal (e : Expr) (n : Nat) : Expr :=
  forallE Name.anonymous (andNE (collectNOrNegArgs e n)) (dropNArgs e n) BinderInfo.default

def getCongAssoc' : Nat → Name → Term
| 0,     n => mkIdent n
| i + 1, n => Syntax.mkApp (mkIdent `congOrLeft) #[getCongAssoc' i n]

def getCongAssoc : Nat → Name → List Term
| 0,     _ => []
| 1,     n => [getCongAssoc' 0 n]
| i + 2, n => (getCongAssoc' (i + 1) n) :: (getCongAssoc (i + 1) n)

def getLength (o : Expr) : Nat :=
  match o with
  | app (app (const `Or ..) _) e2 => 1 + getLength e2
  | _ => 1

def getNatLit? : Lean.Expr → Option Nat
| app (app _ (lit (Lean.Literal.natVal x))) _ => some x
| _ => none

def collectPropsInOrChain : Expr → List Expr
| app (app (const `Or ..) e₁) e₂ => e₁ :: collectPropsInOrChain e₂
| e => [e]

def createOrChain : List Expr → Expr
| [] => mkConst `unreachable
| [h] => h
| h::t => app (app (mkConst `Or) h) $ createOrChain t

def getGroupOrPrefixGoal : Expr → Nat → Expr
| e, n => let props := collectPropsInOrChain e
          let left := createOrChain (List.take n props)
          let right := createOrChain (List.drop n props)
          app (app (mkConst `Or) left) right

def listExpr : List Expr → Expr
| [] => mkConst `List.nil
| e::es => mkApp (mkApp (mkConst `List.cons) e) (listExpr es)

syntax (name := groupOrPrefix) "groupOrPrefix" term "," term "," ident : tactic

@[tactic groupOrPrefix] def evalGroupOrPrefix : Tactic := fun stx => withMainContext do
  let hyp ← Tactic.elabTerm stx[1] none
  let prefLen ← 
    match ← getNatLit? <$> Tactic.elabTerm stx[3] none with
    | Option.some i => pure i
    | Option.none   => throwError "[groupOrPrefix]: second argument must be a nat lit"
  let type ← Meta.inferType hyp
  let l := getLength type
  if prefLen > 1 && prefLen < l then
    let mvarId ← getMainGoal
    Meta.withMVarContext mvarId do
      let name := stx[5].getId
      let newTerm := getGroupOrPrefixGoal type prefLen
      let p ← Meta.mkFreshExprMVar newTerm MetavarKind.syntheticOpaque name
      let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name newTerm p
      replaceMainGoal [p.mvarId!, mvarIdNew]
    for t in List.reverse (getCongAssoc (prefLen - 1) `orAssocDir) do
      evalTactic  (← `(tactic| apply $t))
    Tactic.closeMainGoal hyp
  else throwError "[groupOrPrefix]: prefix length must be > 1 and < size of or-chain"


def exprToString : Expr → String
| bvar id        => s!"(BVAR {id})"
| fvar id        => s!"(FVAR {id.name})"
| mvar id        => s!"(MVAR {id.name})"
| sort l         => s!"(SORT {l})"
| const id l     => s!"(CONST {id} {l})"
| app f x        => s!"(APP {exprToString f} {exprToString x})"
| lam id s e _   => s!"(LAM {id} {exprToString s} {exprToString e})"
| forallE id s e _ => s!"(FORALL {id} {exprToString s} {exprToString e})"
| letE id s v e _  =>
  s!"(LET {id} {exprToString s} {exprToString v} {exprToString e})"
| lit l          => s!"(LIT {literalToString l})"
| mdata m e      => s!"(MDATA {m} {exprToString e})"
| proj s i e     => s!"(PROJ {s} {i} {exprToString e})"
where
  literalToString : Literal → String
    | Literal.natVal v => ⟨Nat.toDigits 10 v⟩
    | Literal.strVal v => v

syntax (name := liftNOrToImp) "liftNOrToImp" term "," term "," ident : tactic

#check Expr

@[tactic liftNOrToImp] def evalLiftNOrToImp : Tactic :=
  fun stx => withMainContext do
    let prefLen ← 
      match ← getNatLit? <$> Tactic.elabTerm stx[3] none with
      | Option.some i => pure i
      | Option.none   => throwError "[liftNOrToImp]: second argument must be a nat lit"
    let tstx₁ : Term := ⟨stx[1]⟩
    let tstx₃ : Term := ⟨stx[3]⟩
    let fname1 ← mkIdent <$> mkFreshId
    let hyp ← inferType (← Tactic.elabTerm stx[1] none)
    let _ ← evalTactic (← `(tactic| groupOrPrefix $tstx₁, $tstx₃, $fname1))
    let mvarId ← getMainGoal
    Meta.withMVarContext mvarId do
      let name := stx[5].getId
      let goal := liftNOrToImpGoal hyp prefLen
      let hyp ← instantiateMVars hyp
      logInfo m!"goal = {goal}"
      logInfo m!"hyp = {exprToString hyp}"
      let p ← Meta.mkFreshExprMVar goal MetavarKind.syntheticOpaque name
      let (_, mvarIdNew) ← Meta.intro1P $ ← Meta.assert mvarId name goal p
      replaceMainGoal [p.mvarId!, mvarIdNew]
    withMainContext do
      let ctx ← getLCtx
      let grouped ← inferType (ctx.findFromUserName? fname1.getId).get!.toExpr
      let v : Expr := mkApp (mkConst `orImplies₃) grouped
      let li := listExpr $ collectNOrNegArgs hyp prefLen
      let u : Expr := mkApp (mkConst `deMorgan₂) li
      -- seems better to close the goal by crafting the proof term instead
      -- of using apply
      Tactic.closeMainGoal (mkApp (mkApp (mkConst `Function.comp) v) u)
      let _ ← evalTactic (← `(tactic| clear $fname1))

/- example : ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D → A ∧ B ∧ C → ¬ D := by -/
/-   intros h₁ h₂ -/

/-   liftNOrToImp h₁, 3, bla -/
/-   exact bla h₂ -/
  /- have h₃ : (¬ A ∨ ¬ B ∨ ¬ C) ∨ ¬ D := sorry -- por meio de taticas -/
  /- have bla : ¬ (¬ A ∨ ¬ B ∨ ¬ C) → ¬ D := orImplies₃ h₃ -/
  /- admit -/

  /- have ble : A ∧ B ∧ C → ¬ (¬ A ∨ ¬ B ∨ ¬ C) := @deMorgan₂ [A, B, C] -/
  /- have bli : A ∧ B ∧ C → ¬ D := bla ∘ ble -/
  /- exact bla (ble h₂) -/
  
-- hipotese ble: A ∧ B ∧ C → ¬ D
