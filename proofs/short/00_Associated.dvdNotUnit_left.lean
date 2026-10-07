/-
Machine-generated proof, verified by Lean.

Theorem:      Associated.dvdNotUnit_left
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/GroupWithZero/Associated.lean, line 765
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem Associated.dvdNotUnit_left (h : DvdNotUnit p r) (h' : Associated p q) :
    DvdNotUnit q r := by
  obtain ⟨u, rfl⟩ := h'
  obtain ⟨hp, x, hx, rfl⟩ := h
  refine ⟨fun h0 => hp ?_, ↑u⁻¹ * x, mt isUnit_of_mul_isUnit_right hx, ?_⟩
  · first
      | simpa using congrArg (· * (↑u⁻¹ : M)) h0
      | exact (Units.mul_right_eq_zero u).mp h0
  · first
      | rw [mul_assoc, Units.mul_inv_cancel_left]
      | simp [mul_assoc]
