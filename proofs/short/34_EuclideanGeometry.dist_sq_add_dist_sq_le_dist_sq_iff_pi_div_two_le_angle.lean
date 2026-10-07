/-
Machine-generated proof, verified by Lean.

Theorem:      EuclideanGeometry.dist_sq_add_dist_sq_le_dist_sq_iff_pi_div_two_le_angle
Source:       Mathlib @ d0a050ad6, Mathlib/Geometry/Euclidean/Angle/Unoriented/RightAngle.lean, line 338
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Geometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem dist_sq_add_dist_sq_le_dist_sq_iff_pi_div_two_le_angle {p₁ p₂ p₃ : P} :
    dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ≤ dist p₁ p₃ * dist p₁ p₃ ↔
      π / 2 ≤ ∠ p₁ p₂ p₃ := by
  have key : ∀ t : ℝ, π / 2 ≤ Real.arccos t ↔ t ≤ 0 := fun t => by
    rw [← not_lt, Real.arccos_lt_pi_div_two, not_lt]
  have hv : ∀ x y : V, ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ≤ ‖x - y‖ * ‖x - y‖ ↔
      π / 2 ≤ InnerProductGeometry.angle x y := by
    intro x y
    have e := norm_sub_mul_self_real x y
    have hi := real_inner_le_norm x y
    rw [InnerProductGeometry.angle, key]
    rcases (mul_nonneg (norm_nonneg x) (norm_nonneg y)).eq_or_lt with h | h
    · rw [← h, div_zero]
      constructor
      · intro _
        exact le_rfl
      · intro _
        linarith
    · rw [div_le_iff₀ h, zero_mul]
      constructor <;> intro _ <;> linarith
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂, dist_eq_norm_vsub V p₁ p₃,
    ← vsub_sub_vsub_cancel_right p₁ p₃ p₂, EuclideanGeometry.angle]
  exact hv _ _
