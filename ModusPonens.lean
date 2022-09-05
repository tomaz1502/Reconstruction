import Meta

theorem notImplies1 : ∀ {P Q : Prop}, ¬ (P → Q) → P := by
  intros P Q h
  cases Classical.em P with
  | inl p  => exact p
  | inr np => apply False.elim
              apply h
              intro p
              exact False.elim (np p)

theorem notImplies2 : ∀ {P Q : Prop}, ¬ (P → Q) → ¬ Q := by
  intros P Q h
  cases Classical.em Q with
  | inl q  => exact False.elim (h (λ _ => q))
  | inr nq => exact nq

theorem impliesElim : ∀ {P Q : Prop}, (P → Q) → ¬ P ∨ Q := by
  intros P Q h
  cases Classical.em P with
  | inl p  => exact Or.inr (h p)
  | inr np => exact Or.inl np

theorem contradiction : ∀ {P : Prop}, P → ¬ P → False := λ p np => np p

theorem mpCvc5 (P Q : Prop) : ¬ (P → (P → Q) → Q) → False :=
  λ lean_a0 =>
    have lean_s0 := notImplies2 lean_a0
    have lean_s1 := notImplies1 lean_s0
    have lean_s2 := impliesElim lean_s1
    have lean_s4 := notImplies1 lean_a0
    have lean_s6 : Q := by resolution lean_s4, lean_s2, P, x; exact x
    have lean_s9 := notImplies2 lean_s0
    contradiction lean_s6 lean_s9

theorem doubleNeg : ∀ {P : Prop}, ¬ ¬ P → P := by
  intros P h
  cases Classical.em P with
  | inl p => exact p
  | inr np => exact False.elim (h np)

theorem mp : ∀ (P Q : Prop), P → (P → Q) → Q := λ P Q => doubleNeg (mpCvc5 P Q)
