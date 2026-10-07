/-
Machine-generated proof, verified by Lean.

Theorem:      Submodule.orthogonalProjectionOnto_eq_zero_iff
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean, line 317
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem orthogonalProjectionOnto_eq_zero_iff {v : E} :
    K.orthogonalProjectionOnto v = 0 ↔ v ∈ Kᗮ := by
  constructor
  · intro h
    have h' : K.starProjection v = 0 := by
      first
        | simpa using congrArg Subtype.val h
        | (rw [starProjection_apply, h]; try rfl)
    simpa [h'] using sub_starProjection_mem_orthogonal (K := K) v
  · intro h
    have h' : K.starProjection v = 0 :=
      eq_starProjection_of_mem_orthogonal (zero_mem K) (by simpa using h)
    first
      | exact Subtype.ext h'
      | (ext; simpa using h')
