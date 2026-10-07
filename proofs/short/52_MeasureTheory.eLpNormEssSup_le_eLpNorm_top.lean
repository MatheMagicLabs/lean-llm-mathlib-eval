/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.eLpNormEssSup_le_eLpNorm_top
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean, line 141
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem eLpNormEssSup_le_eLpNorm_top [TopologicalSpace ε] {f : α → ε} :
    eLpNormEssSup f μ ≤ eLpNorm f ∞ μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (eLpNorm_exponent_top hf).symm.le
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top
