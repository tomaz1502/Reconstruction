universe u

theorem instForAll {A : Type u} {f : A → Prop} {a : A} :
  (forall a' : A, f a') → f a := by
  intro h
  exact h a

theorem zulipHaniel₁ {A : Type u} {P : A → Prop} {t : A} :
  (forall x : A, x = t → P x) → P t := by
  intro h
  exact h t rfl

theorem zulipHaniel₂ {A : Type u} {P : A → Prop} {t : A} :
  P t → (forall x : A, x = t → P x) := by
  intros h x r
  rewrite [r]
  exact h

theorem zulipHaniel {A : Type u} {P : A → Prop} {t : A} :
  (forall x : A, x = t → P x) ↔ P t := ⟨zulipHaniel₁, zulipHaniel₂⟩

