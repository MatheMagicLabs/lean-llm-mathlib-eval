/-
Machine-generated proof, verified by Lean.

Theorem:      AffineSubspace.finDim_eq_finrank_of_not_finite
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/AffineSpace/Dimension.lean, line 96
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem finDim_eq_finrank_of_not_finite [Module.Free R s.direction] [StrongRankCondition R]
    (h : ¬Module.Finite R s.direction) : finDim s = 0 := by
  have hs : s ≠ ⊥ := by
    rintro rfl
    apply h
    rw [direction_bot]
    first
      | infer_instance
      | exact Module.Finite.iff_fg.mpr Submodule.fg_bot
      | exact Module.Finite.of_finite
  have h0 : Module.finrank R s.direction = 0 := by
    first
      | exact Module.finrank_of_not_finite h
      | (rw [Module.finrank, Cardinal.toNat_eq_zero]
         exact Or.inr (not_lt.1 (mt Module.rank_lt_aleph0_iff.1 h)))
  simp [finDim_eq_finrank hs, h0]
