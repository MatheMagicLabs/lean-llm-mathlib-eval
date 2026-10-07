/-
Machine-generated proof, verified by Lean.

Theorem:      ZeroAtInftyContinuousMap.unitizationEquiv_neg
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/ContinuousMap/ZeroAtInftyUnitization.lean, line 289
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma unitizationEquiv_neg (f : Unitization R C₀(X, R)) :
    unitizationEquiv X R (-f) = -unitizationEquiv X R f := by
  first
    | (rw [eq_neg_iff_add_eq_zero, ← unitizationEquiv_add, neg_add_cancel, unitizationEquiv_zero]; done)
    | (ext x; induction x using OnePoint.rec <;> simp <;> abel)
    | (ext x; induction x using OnePoint.rec <;> simp [neg_add])
