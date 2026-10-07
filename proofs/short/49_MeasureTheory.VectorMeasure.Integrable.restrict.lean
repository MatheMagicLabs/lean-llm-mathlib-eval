/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.Integrable.restrict
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Integral.lean, line 503
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (7.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma Integrable.restrict (hf : μ.Integrable f) {s : Set X} :
    (μ.restrict s).Integrable f := by
  by_cases hs : MeasurableSet s
  · apply MeasureTheory.Integrable.mono_measure hf
    first
    | exact variation_restrict_le μ s
    | exact variation_restrict_le s
    | exact variation_restrict_le
    | (rw [variation_restrict hs]; exact Measure.restrict_le_self)
    | (rw [variation_restrict μ hs]; exact Measure.restrict_le_self)
    | (rw [variation_restrict _ hs]; exact Measure.restrict_le_self)
    | (rw [variation_restrict hs μ]; exact Measure.restrict_le_self)
    | (rw [restrict_variation hs]; exact Measure.restrict_le_self)
    | (rw [restrict_variation μ hs]; exact Measure.restrict_le_self)
    | (simp [variation_restrict, hs, Measure.restrict_le_self]; done)
  · rw [restrict_not_measurable μ hs]
    exact Integrable.zero_vectorMeasure
