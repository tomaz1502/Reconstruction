import Meta.Boolean
import Meta.Resolution
import Meta.PermutateOr
 
universe u
 
variable {U : Type u}
 
variable {f : U → U → U}
 
variable {p₁ p₂ p₃ : Prop}
 
variable {a b c d : U}

theorem euf : (a = b) → (c = d) → p₁ ∧ True → (¬ p₁) ∨ (p₂ ∧ p₃) → (¬ p₃) ∨ (¬ (f a c = f b d)) → False :=
  fun lean_a0 : (a = b) =>
  fun lean_a1 : (c = d) =>
  fun lean_a2 : p₁ ∧ True =>
  fun lean_a3 : (¬ p₁) ∨ (p₂ ∧ p₃) =>
  fun lean_a4 : (¬ p₃) ∨ (¬ (f a c = f b d)) =>
    have lean_s0 : ((a = b) ∧ (c = d)) ∨ ¬ (a = b) ∨ (¬ (c = d)) := cnfAndNeg [(a = b), (c = d)]
    have lean_s1 : ¬ (a = b) ∨ (¬ (c = d)) ∨ (f a c = f b d) :=
      scope (λ lean_a5 : (a = b) =>
        (scope (λ lean_a6 : (c = d) =>
          let lean_s1 : f = f := rfl
          have lean_s2 : b = a := Eq.symm lean_a5
          have lean_s3 : (a = b) := Eq.symm lean_s2
          let lean_s4 := cong lean_s1 lean_s3
          have lean_s5 : d = c := Eq.symm lean_a6
          have lean_s6 : (c = d) := Eq.symm lean_s5
          have lean_s7 : (f a c = f b d) := cong lean_s4 lean_s6
          show (f a c = f b d) from lean_s7
        )
      ))
    have lean_s2 : a = b ∧ c = d → f a c = f b d := by liftOrNToImp lean_s1, 2
    have lean_s3 : (¬ ((a = b) ∧ (c = d))) ∨ (f a c = f b d) := impliesElim lean_s2
    have lean_s5 : ¬ (a = b) ∨ ¬ (c = d) ∨ f a c = f b d := by resolutionZ lean_s0, lean_s3, ((a = b) ∧ (c = d))
    have lean_s6 : f a c = f b d ∨ ¬ (a = b) ∨ ¬ (c = d) := by permutateOr lean_s5, [2, 0, 1]
    have lean_s7 := lean_a4
    have lean_s8 : (¬ (p₂ ∧ p₃)) ∨ p₃ := @cnfAndPos ([p₂, p₃]) 1
    have lean_s9 : p₃ ∨ (¬ (p₂ ∧ p₃)) := by permutateOr lean_s8, [1, 0]
    have lean_s10 := lean_a3
    have lean_s11 : (p₁ ∧ True) = p₁ := sorry
    have lean_s12 : p₁ := eqResolve lean_a2 lean_s11
    have lean_s13 := lean_s12
    have lean_s14 : p₂ ∧ p₃ := by resolutionO lean_s10, lean_s13, p₁
    have lean_s15 : p₃ := by resolutionO lean_s9, lean_s14, (p₂ ∧ p₃)
    have lean_s16 : ¬ (f a c = f b d) := by resolutionO lean_s7, lean_s15, p₃
    have lean_s17 : ¬ (a = b) ∨ ¬ (c = d) := by resolutionZ lean_s6, lean_s16, (f a c = f b d)
    sorry
 
