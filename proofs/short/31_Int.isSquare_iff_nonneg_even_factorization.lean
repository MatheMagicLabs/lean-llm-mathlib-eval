/-
Machine-generated proof, verified by Lean.

Theorem:      Int.isSquare_iff_nonneg_even_factorization
Source:       Mathlib @ d0a050ad6, Mathlib/Data/Nat/Factorization/Defs.lean, line 215
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  6 tactic steps; area: Data
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem isSquare_iff_nonneg_even_factorization {n : ℤ} :
    IsSquare n ↔ 0 ≤ n ∧ ∀ (p : ℕ), p.Prime → Even (n.natAbs.factorization p) := by
  constructor
  · rintro ⟨m, rfl⟩
    have hsq : IsSquare (m * m).natAbs := by
      first
      | exact ⟨m.natAbs, Int.natAbs_mul m m⟩
      | exact ⟨m.natAbs, by rw [Int.natAbs_mul]⟩
      | exact ⟨m.natAbs, by simp⟩
    refine ⟨?_, Nat.isSquare_iff_even_factorization.mp hsq⟩
    first
    | exact _root_.mul_self_nonneg m
    | exact Int.mul_self_nonneg m
    | exact (Int.le_total 0 m).elim (fun hm => Int.mul_nonneg hm hm)
        (fun hm => Int.mul_nonneg_of_nonpos_of_nonpos hm hm)
  · rintro ⟨h0, h⟩
    obtain ⟨k, hk⟩ := Nat.isSquare_iff_even_factorization.mpr h
    refine ⟨(k : ℤ), ?_⟩
    have h1 : ((n.natAbs : ℕ) : ℤ) = n := by
      first
      | exact Int.natAbs_of_nonneg h0
      | simp [abs_of_nonneg h0]
      | simp [h0]
    first
    | (rw [← h1, hk, Nat.cast_mul]; done)
    | (rw [← h1]; exact_mod_cast hk)
    | (rw [← h1, hk]; exact Nat.cast_mul k k)
    | (rw [← h1, hk]; push_cast; done)
    | (rw [← h1, hk]; simp)
