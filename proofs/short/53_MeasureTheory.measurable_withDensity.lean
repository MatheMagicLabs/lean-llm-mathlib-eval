/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.measurable_withDensity
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Measure/WithDensity.lean, line 379
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem measurable_withDensity {β : Type*} [MeasurableSpace β] {f : β → α → ℝ≥0∞}
    [SFinite μ] (hf : Measurable f.uncurry) :
    Measurable fun b ↦ μ.withDensity (f b) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [withDensity_apply _ hs]
  first
  | exact hf.lintegral_prod_right
  | exact Measurable.lintegral_prod_right hf
  | exact hf.lintegral_prod_right'
  | fun_prop
