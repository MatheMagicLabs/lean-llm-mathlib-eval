/-
Machine-generated proof, verified by Lean.

Theorem:      Function.locallyFinsuppWithin.sum_toClosedBall_le_logCounting
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean, line 254
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  61 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem sum_toClosedBall_le_logCounting {D : Function.locallyFinsupp ℂ ℤ} {ρ r : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρr : ρ < r) :
    (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * Real.log (r / ρ) ≤ D.logCounting r := by
  have hr : 0 < r := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hlog : log (r / ρ) ≤ log r := by
    rw [Real.log_div hr.ne' hρ0.ne']
    linarith [Real.log_nonneg hρ]
  have hsub : closedBall (0 : ℂ) |ρ| ⊆ closedBall 0 |r| := by
    apply closedBall_subset_closedBall
    rw [abs_of_pos hρ0, abs_of_pos hr]
    exact hρr.le
  have h0ρ : (0 : ℂ) ∈ closedBall (0 : ℂ) |ρ| := mem_closedBall_self (abs_nonneg ρ)
  have hs : (toClosedBall r D).support.Finite :=
    (toClosedBall r D).finiteSupport (isCompact_closedBall 0 |r|)
  classical
  have hzero : ∀ z : ℂ, z ∉ insert (0 : ℂ) hs.toFinset →
      toClosedBall ρ D z = 0 ∧ toClosedBall r D z = 0 := by
    intro z hz
    rw [Finset.mem_insert, not_or, Set.Finite.mem_toFinset] at hz
    have h₁ : toClosedBall r D z = 0 := by
      by_contra h
      exact hz.2 (Function.mem_support.2 h)
    refine ⟨?_, h₁⟩
    by_cases hzρ : z ∈ closedBall (0 : ℂ) |ρ|
    · rw [toClosedBall_eval_within D hzρ]
      rwa [toClosedBall_eval_within D (hsub hzρ)] at h₁
    · exact apply_eq_zero_of_notMem (toClosedBall ρ D) hzρ
  have hpt : ∀ z : ℂ, z ≠ 0 →
      ((toClosedBall ρ D z : ℤ) : ℝ) * log (r / ρ) ≤
        ((toClosedBall r D z : ℤ) : ℝ) * log (r * ‖z‖⁻¹) := by
    intro z hz0
    by_cases hzρ : z ∈ closedBall (0 : ℂ) |ρ|
    · rw [toClosedBall_eval_within D hzρ, toClosedBall_eval_within D (hsub hzρ)]
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hr hρ0) ?_)
        (Int.cast_nonneg (hD z))
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hr.le
      rw [mem_closedBall, dist_zero_right, abs_of_pos hρ0] at hzρ
      first
        | exact inv_anti₀ (norm_pos_iff.2 hz0) hzρ
        | exact (inv_le_inv₀ hρ0 (norm_pos_iff.2 hz0)).2 hzρ
    · rw [apply_eq_zero_of_notMem (toClosedBall ρ D) hzρ, Int.cast_zero, zero_mul]
      by_cases hzr : z ∈ closedBall (0 : ℂ) |r|
      · rw [toClosedBall_eval_within D hzr]
        refine mul_nonneg (Int.cast_nonneg (hD z)) (Real.log_nonneg ?_)
        rw [le_mul_inv_iff₀ (norm_pos_iff.2 hz0), one_mul]
        rw [mem_closedBall, dist_zero_right, abs_of_pos hr] at hzr
        exact hzr
      · simp [apply_eq_zero_of_notMem (toClosedBall r D) hzr]
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset (s := insert (0 : ℂ) hs.toFinset),
    finsum_eq_sum_of_support_subset (s := insert (0 : ℂ) hs.toFinset)]
  rotate_left
  · rw [Function.support_subset_iff']
    intro z hz
    have h := hzero z (fun h ↦ hz (Finset.mem_coe.2 h))
    simp [h.1, h.2]
  · rw [Function.support_subset_iff']
    intro z hz
    have h := hzero z (fun h ↦ hz (Finset.mem_coe.2 h))
    simp [h.1, h.2]
  rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self (0 : ℂ) hs.toFinset),
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self (0 : ℂ) hs.toFinset), add_right_comm]
  refine add_le_add ?_ (Finset.sum_le_sum fun z hz ↦ hpt z (Finset.ne_of_mem_erase hz))
  rw [toClosedBall_eval_within D h0ρ]
  simp only [norm_zero, inv_zero, mul_zero, Real.log_zero, zero_add]
  exact mul_le_mul_of_nonneg_left hlog (Int.cast_nonneg (hD 0))
