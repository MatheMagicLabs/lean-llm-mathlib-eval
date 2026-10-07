/-
Machine-generated proof, verified by Lean.

Theorem:      WeierstrassCurve.t_integral_of_u_integral
Source:       Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean, line 229
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: AlgebraicGeometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma t_integral_of_u_integral : ∃ t : R, algebraMap R K t = CK.t := by
  rcases r_integral_of_u_integral hCK hu with ⟨r, hr⟩
  have hu0 : (CK.u : K) ≠ 0 := CK.u.ne_zero
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 +
    C ((integralModel R W).a₃ + r * (integralModel R W).a₁) * X +
    C (u ^ 6 * (integralModel R W').a₆ - (integralModel R W).a₆ - r * (integralModel R W).a₄ -
      r ^ 2 * (integralModel R W).a₂ - r ^ 3), by monicity!, ?_⟩
  first
  | simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
      integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
    ring1
  | simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
      integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
    field_simp
    ring1
  | simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
      integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
