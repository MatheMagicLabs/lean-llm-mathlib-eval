/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.SignedMeasure.norm_le_totalVariation
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Variation/SignedMeasure.lean, line 34
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem norm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ ≤ s.totalVariation.real i := by
  by_cases hi : MeasurableSet i
  · have key : s i = s.toJordanDecomposition.posPart.real i -
        s.toJordanDecomposition.negPart.real i := by
      conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      first
      | rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
          Measure.toSignedMeasure_apply_measurable hi, Measure.toSignedMeasure_apply_measurable hi]
        try rfl
        done
      | simp [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_apply_measurable hi,
          measureReal_def]
        done
      | simp [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_apply, hi,
          measureReal_def]
    have htv : s.totalVariation.real i = s.toJordanDecomposition.posPart.real i +
        s.toJordanDecomposition.negPart.real i := by
      first
      | simp only [totalVariation, measureReal_def, Measure.add_apply]
        exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
      | rw [totalVariation, measureReal_add_apply]
      | simp [totalVariation, measureReal_def, ENNReal.toReal_add]
    have h1 : 0 ≤ s.toJordanDecomposition.posPart.real i := measureReal_nonneg
    have h2 : 0 ≤ s.toJordanDecomposition.negPart.real i := measureReal_nonneg
    rw [key, htv, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · rw [VectorMeasure.not_measurable s hi, norm_zero]
    exact measureReal_nonneg
