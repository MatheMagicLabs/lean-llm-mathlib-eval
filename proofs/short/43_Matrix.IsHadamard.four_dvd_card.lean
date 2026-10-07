/-
Machine-generated proof, verified by Lean.

Theorem:      Matrix.IsHadamard.four_dvd_card
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/HadamardMatrix.lean, line 242
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  18 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem IsHadamard.four_dvd_card {A : Matrix n n ℤ}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  obtain ⟨i₁, i₂, i₃, h12, h13, h23⟩ := Fintype.two_lt_card_iff.mp hcard
  have hpm : ∀ i j, A i j = 1 ∨ A i j = -1 := by
    intro i j
    have h := (Unitary.mem_iff.mp (hA.apply_mem i j)).2
    first
    | exact Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ h)
    | exact Int.eq_one_or_neg_one_of_mul_eq_one h
  have hrow : ∀ i k, ∑ j, A i j * A k j = (A * Aᴴ) i k := by
    intro i k
    first
    | (rw [Matrix.mul_apply]; rfl)
    | (rw [Matrix.mul_apply]; done)
    | (simp [Matrix.mul_apply]; done)
  have d11 : ∑ j, A i₁ j * A i₁ j = Fintype.card n := by
    rw [hrow, hA.mul_conjTranspose]
    simp
  have o13 : ∑ j, A i₁ j * A i₃ j = 0 := by
    rw [hrow, hA.mul_conjTranspose]
    simp [h13]
  have o21 : ∑ j, A i₂ j * A i₁ j = 0 := by
    rw [hrow, hA.mul_conjTranspose]
    simp [Ne.symm h12]
  have o23 : ∑ j, A i₂ j * A i₃ j = 0 := by
    rw [hrow, hA.mul_conjTranspose]
    simp [h23]
  have key : ∑ j, (A i₁ j + A i₂ j) * (A i₁ j + A i₃ j) = Fintype.card n := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib, d11, o13, o21, o23, add_zero, zero_add]
  have hdvd : (4 : ℤ) ∣ ∑ j, (A i₁ j + A i₂ j) * (A i₁ j + A i₃ j) := by
    apply Finset.dvd_sum
    intro j _
    rcases hpm i₁ j with h1 | h1 <;> rcases hpm i₂ j with h2 | h2 <;>
      rcases hpm i₃ j with h3 | h3 <;> norm_num [h1, h2, h3]
  rw [key] at hdvd
  exact_mod_cast hdvd
