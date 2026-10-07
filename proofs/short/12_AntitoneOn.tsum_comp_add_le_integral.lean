/-
Machine-generated proof, verified by Lean.

Theorem:      AntitoneOn.tsum_comp_add_le_integral
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/SumIntegralComparisons.lean, line 254
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem AntitoneOn.tsum_comp_add_le_integral (N : ℕ) (anti : AntitoneOn f (Ici (N : ℝ)))
    (integrable : IntegrableOn f (Ioi (N : ℝ))) (nonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t) :
    ∑' (n : ℕ),  f (n + N + 1 : ℕ) ≤ ∫ x in Ioi (N : ℝ), f x := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    apply nonneg
    rw [Set.mem_Ioi]
    exact Nat.cast_lt.mpr (by omega)
  · intro M
    calc ∑ i ∈ Finset.range M, f (i + N + 1 : ℕ)
        = ∑ n ∈ Finset.Ico N (N + M), f (n + 1 : ℕ) := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Nat.add_comm N k]
      _ ≤ _ := (anti.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral integrable nonneg
