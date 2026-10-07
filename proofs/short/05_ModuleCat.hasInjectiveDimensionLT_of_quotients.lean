/-
Machine-generated proof, verified by Lean.

Theorem:      ModuleCat.hasInjectiveDimensionLT_of_quotients
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/Category/ModuleCat/Ext/Baer.lean, line 142
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma hasInjectiveDimensionLT_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext ↧(Shrink.{v} (R ⧸ I)) M n)) :
    HasInjectiveDimensionLT M n := by
  cases n with
  | zero =>
    have : Subsingleton M := subsingleton_of_ext_quotient_bot_zero M (h ⊥)
    have hM : Limits.IsZero M := ModuleCat.isZero_of_subsingleton M
    first
      | exact (hasInjectiveDimensionLT_zero_iff_isZero M).mpr hM
      | exact hasInjectiveDimensionLT_zero_iff_isZero.mpr hM
      | (rw [hasInjectiveDimensionLT_zero_iff_isZero]; exact hM)
      | exact hM.hasInjectiveDimensionLT 0
  | succ n => exact hasInjectiveDimensionLE_of_quotients M n h
