/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.exists_one_le_enorm_apply_of_semivariation_eq_top
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Variation/Semivariation.lean, line 106
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  24 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma exists_one_le_enorm_apply_of_semivariation_eq_top
    (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semivariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ := by
  have ha : 2 * (‖μ s‖ₑ + 1) < μ.semivariation s := by
    rw [h's]
    first
      | exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (by simp) (by simp))
      | (simp; done)
      | exact ENNReal.mul_lt_top (by simp) (by simp)
  obtain ⟨t, ts, t_meas, ht⟩ := exists_subset_lt_enorm_apply_of_lt_semivariation hs ha
  have h1 : ‖μ s‖ₑ + 1 < ‖μ t‖ₑ := by
    by_contra! hle
    exact lt_irrefl _ (ht.trans_le (by gcongr))
  have h1' : 1 ≤ ‖μ t‖ₑ := le_add_self.trans h1.le
  have h2 : 1 ≤ ‖μ (s \ t)‖ₑ := by
    have e : μ t = μ s - μ (s \ t) := by
      rw [eq_sub_iff_add_eq, of_add_of_diff t_meas hs ts]
    have h3 : ‖μ t‖ₑ ≤ ‖μ s‖ₑ + ‖μ (s \ t)‖ₑ := by
      rw [e]
      first
        | exact enorm_sub_le
        | exact enorm_sub_le _ _
        | (rw [sub_eq_add_neg]; exact (enorm_add_le _ _).trans (le_of_eq (by rw [enorm_neg])))
    by_contra! hlt
    have hle : ‖μ (s \ t)‖ₑ ≤ 1 := hlt.le
    have h4 : ‖μ s‖ₑ + ‖μ (s \ t)‖ₑ ≤ ‖μ s‖ₑ + 1 := by gcongr
    exact lt_irrefl _ (h1.trans_le (h3.trans h4))
  have hsplit : μ.semivariation s ≤ μ.semivariation t + μ.semivariation (s \ t) := by
    calc μ.semivariation s = μ.semivariation (t ∪ (s \ t)) := by rw [Set.union_diff_cancel ts]
      _ ≤ μ.semivariation t + μ.semivariation (s \ t) := semivariation_union_le
  rw [h's] at hsplit
  rcases ENNReal.add_eq_top.1 (top_le_iff.1 hsplit) with hT | hD
  · exact ⟨t, t_meas, ts, hT, h2⟩
  · refine ⟨s \ t, hs.diff t_meas, fun _ hx => hx.1, hD, ?_⟩
    rw [Set.diff_diff_cancel_left ts]
    exact h1'
