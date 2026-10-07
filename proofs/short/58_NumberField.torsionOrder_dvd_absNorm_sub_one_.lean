/-
Machine-generated proof, verified by Lean.

Theorem:      NumberField.torsionOrder_dvd_absNorm_sub_one'
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/NumberField/Ideal/Basic.lean, line 192
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  13 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem NumberField.torsionOrder_dvd_absNorm_sub_one' {P : Ideal (𝓞 K)} [hP : P.IsPrime]
    (hP₁ : Algebra.IsUnramifiedAt ℤ P) (hP₂ : absNorm (under ℤ P) ≠ 2) :
    torsionOrder K ∣ absNorm P - 1 := by
  by_cases hP₀ : P = ⊥
  · first
    | simp [hP₀]
    | subst hP₀
      simp
    | rw [hP₀, absNorm_bot]
      simp
  have : NeZero P := by
    first
    | exact ⟨hP₀⟩
    | exact ⟨fun h ↦ hP₀ (by simpa using h)⟩
    | exact ⟨fun h ↦ hP₀ (h.trans Ideal.zero_eq_bot)⟩
  have hp := Nat.absNorm_under_prime P
  have h2 : 2 < absNorm (under ℤ P) := by
    have := hp.two_le
    omega
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP
  let _ := Ideal.Quotient.field P
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective' hP₁ h2)
  rwa [Nat.card_units] at h
