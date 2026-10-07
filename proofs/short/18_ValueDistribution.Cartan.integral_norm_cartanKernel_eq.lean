/-
Machine-generated proof, verified by Lean.

Theorem:      ValueDistribution.Cartan.integral_norm_cartanKernel_eq
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/Proximity/IntegralPresentation.lean, line 68
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  8 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma integral_norm_cartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α in Ioc 0 (2 * π), ‖cartanKernel f R α β‖ =
      2 * (∫ α, (cartanKernel f R α β)⁺ ∂(volume.restrict (Ioc 0 (2 * π)))) -
        (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
  have hk : IntegrableOn (fun α ↦ cartanKernel f R α β) (Ioc 0 (2 * π)) :=
    integrableOn_cartanKernel_left f R β
  have h3 : circleAverage (fun z ↦ log ‖z - f (circleMap 0 R β)‖) 0 1 =
      log⁺ ‖f (circleMap 0 R β)‖ := by
    first
    | exact circleAverage_log_norm_sub_const_eq_posLog
    | exact circleAverage_log_norm_sub_const_eq_posLog _
    | rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog one_ne_zero]
      simp
    | simp
  have h1 : ∫ α in Ioc 0 (2 * π), cartanKernel f R α β =
      (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
    first
    | rw [← h3, circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne',
        one_mul, intervalIntegral.integral_of_le two_pi_pos.le]
      simp only [cartanKernel, norm_sub_rev]
      done
    | rw [← h3]
      simp only [circleAverage, smul_eq_mul, mul_inv_cancel_left₀ two_pi_pos.ne',
        intervalIntegral.integral_of_le two_pi_pos.le, cartanKernel, norm_sub_rev]
      done
    | rw [← h3, circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne',
        one_mul, intervalIntegral.integral_of_le two_pi_pos.le]
      congr 1
      ext α
      simp only [cartanKernel]
      rw [norm_sub_rev]
  have h2 : (fun α ↦ (cartanKernel f R α β)⁺) =
      fun α ↦ (‖cartanKernel f R α β‖ + cartanKernel f R α β) / 2 := by
    ext α
    rcases le_total 0 (cartanKernel f R α β) with h | h
    · rw [Real.norm_eq_abs, abs_of_nonneg h]
      first
      | rw [posPart_eq_self.mpr h]
        ring
      | rw [posPart_def, sup_eq_left.mpr h]
        ring
      | simp [h]
        ring
    · rw [Real.norm_eq_abs, abs_of_nonpos h]
      first
      | rw [posPart_eq_zero.mpr h]
        ring
      | rw [posPart_def, sup_eq_right.mpr h]
        ring
      | simp [h]
        ring
  rw [h2]
  first
  | rw [integral_div]
  | simp only [div_eq_mul_inv]
    rw [integral_mul_const]
  rw [integral_add (Integrable.norm hk) hk, h1]
  ring
