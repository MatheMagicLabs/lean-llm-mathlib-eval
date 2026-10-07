/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.preVariationFun_apply_of_ennreal
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Variation/Basic.lean, line 434
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma preVariationFun_apply_of_ennreal (s : Set X) : preVariationFun μ s = μ s := by
  by_cases hs : MeasurableSet s
  · first
    | (rw [preVariationFun, dif_pos hs]; exact iSup_sum_finpartition_parts μ hs)
    | (simp [preVariationFun, hs]; done)
    | (simp only [preVariationFun, hs, dite_true]; exact iSup_sum_finpartition_parts μ hs)
  · first
    | (rw [preVariationFun, dif_neg hs, μ.not_measurable hs])
    | (simp [preVariationFun, hs, μ.not_measurable hs]; done)
