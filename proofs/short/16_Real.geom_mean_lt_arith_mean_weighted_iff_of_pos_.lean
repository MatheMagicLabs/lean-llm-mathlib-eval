/-
Machine-generated proof, verified by Lean.

Theorem:      Real.geom_mean_lt_arith_mean_weighted_iff_of_pos'
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/MeanInequalities.lean, line 292
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem geom_mean_lt_arith_mean_weighted_iff_of_pos' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, z j ≠ ∑ i ∈ s, w i * z i := by
  have h1 := geom_mean_le_arith_mean_weighted s w z (fun i hi => (hw i hi).le) hw' hz
  have h2 := geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz
  constructor
  · intro h
    by_contra H
    apply h.ne
    apply h2.mpr
    intro j hj
    by_contra H'
    exact H ⟨j, hj, H'⟩
  · rintro ⟨j, hj, hne⟩
    refine lt_of_le_of_ne h1 ?_
    intro heq
    exact hne (h2.mp heq j hj)
