/-
Machine-generated proof, verified by Lean.

Theorem:      MvPowerSeries.pderiv_X_of_ne
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPowerSeries/Derivative.lean, line 143
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j) = (0 : MvPowerSeries σ R) := by
  classical
  ext n
  have hn : n + single i 1 ≠ single j 1 := by
    intro hn
    have := DFunLike.congr_fun hn i
    simp [Finsupp.single_apply, h] at this
  first
  | rw [coeff_pderiv, coeff_X, if_neg hn, zero_mul, map_zero]
  | simp [coeff_pderiv, coeff_X, hn]
