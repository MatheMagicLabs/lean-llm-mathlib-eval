/-
Machine-generated proof, verified by Lean.

Theorem:      map_add_eq_sum_add_integral_iteratedFDeriv
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Calculus/TaylorIntegral.lean, line 69
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  54 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem map_add_eq_sum_add_integral_iteratedFDeriv (hf : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
    ContDiffAt ℝ (n + 1) f (x + t • y)) :
    f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _ ↦ y)) +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
  have hderiv : ∀ (k : ℕ) (t : ℝ), ContDiffAt ℝ (k + 1) f (x + t • y) →
      HasDerivAt (fun s : ℝ ↦ iteratedFDeriv ℝ k f (x + s • y) (fun _ ↦ y))
        (iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ ↦ y)) t := by
    intro k t ht
    have hf' : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x + t • y) := by
      apply ht.differentiableAt_iteratedFDeriv
      norm_cast
      exact lt_add_one k
    have h1 : DifferentiableAt ℝ (fun z ↦ iteratedFDeriv ℝ k f z (fun _ ↦ y)) (x + t • y) :=
      hf'.continuousMultilinear_apply_const _
    have h2 : DifferentiableAt ℝ (fun s : ℝ ↦ x + s • y) t := by fun_prop
    have h3 : DifferentiableAt ℝ
        (fun s : ℝ ↦ iteratedFDeriv ℝ k f (x + s • y) (fun _ ↦ y)) t := by
      first
        | (have h4 := h1.comp t h2; exact h4)
        | exact DifferentiableAt.comp (g := fun z ↦ iteratedFDeriv ℝ k f z (fun _ ↦ y)) t h1 h2
        | (have h4 := DifferentiableAt.comp (g := fun z ↦ iteratedFDeriv ℝ k f z (fun _ ↦ y))
            (f := fun s : ℝ ↦ x + s • y) t h1 h2; exact h4)
    rw [← ht.deriv_fderiv_add_smul]
    exact h3.hasDerivAt
  have hcont : ∀ k : ℕ, (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (k + 1) f (x + t • y)) →
      ContinuousOn (fun t : ℝ ↦ iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ ↦ y))
        (Set.uIcc 0 1) := by
    intro k hk t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h0 : ContDiffAt ℝ 0 (iteratedFDeriv ℝ (k + 1) f) (x + t • y) :=
      (hk t ht).iteratedFDeriv_right (by first | simp | (norm_cast; simp) | (push_cast; rfl))
    have h1 : ContinuousAt (iteratedFDeriv ℝ (k + 1) f) (x + t • y) := h0.continuousAt
    have h2 : ContinuousAt (fun s : ℝ ↦ x + s • y) t := by fun_prop
    have h3 : ContinuousAt (fun s : ℝ ↦ iteratedFDeriv ℝ (k + 1) f (x + s • y)) t := by
      first
        | (have h5 := h1.comp_of_eq h2 rfl; exact h5)
        | (have h5 := ContinuousAt.comp (g := iteratedFDeriv ℝ (k + 1) f)
            (f := fun s : ℝ ↦ x + s • y) h1 h2; exact h5)
        | exact h1.comp_of_eq h2 rfl
    have h4 : ContinuousAt
        (fun s : ℝ ↦ iteratedFDeriv ℝ (k + 1) f (x + s • y) (fun _ ↦ y)) t := by
      first
        | exact h3.eval_const (fun _ ↦ y)
        | (have h5 := (continuous_eval_const (fun _ : Fin (k + 1) ↦ y)).continuousAt.comp h3
           exact h5)
        | (have h5 := (ContinuousMultilinearMap.continuous_eval_const
              (fun _ : Fin (k + 1) ↦ y)).continuousAt.comp h3
           exact h5)
        | fun_prop
    exact h4.continuousWithinAt
  revert hf
  induction n with
  | zero =>
    intro hf
    have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hderiv 0 t (hf t (by rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht)))
      (hcont 0 hf).intervalIntegrable
    simp only [pow_zero, one_smul]
    rw [hI]
    simp only [Finset.sum_range_one, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_smul, iteratedFDeriv_zero_apply, zero_smul, add_zero]
    abel
  | succ n ih =>
    intro hf
    have hf' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • y) := fun t ht ↦
      (hf t ht).of_le (by
        first
        | (norm_cast; omega)
        | simp
        | exact_mod_cast Nat.le_succ (n + 1)
        | (push_cast; exact le_self_add)
        | (push_cast; exact le_add_right le_rfl))
    have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ (1 - t) ^ (n + 1)) (-(((n : ℝ) + 1) * (1 - t) ^ n)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) t := (hasDerivAt_id t).const_sub 1
      have h2 := h1.pow (n + 1)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h2
      convert h2 using 1 <;> first | ring | rfl | (funext s; simp)
    have hv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ ↦ iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y))
          (iteratedFDeriv ℝ (n + 1 + 1) f (x + t • y) (fun _ ↦ y)) t := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact hderiv (n + 1) t (hf t ht)
    have hcu : Continuous (fun t : ℝ ↦ (1 - t) ^ (n + 1)) := by fun_prop
    have hcu' : Continuous (fun t : ℝ ↦ -(((n : ℝ) + 1) * (1 - t) ^ n)) := by fun_prop
    have hcv : ContinuousOn (fun t : ℝ ↦ iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y))
        (Set.uIcc 0 1) := hcont n hf'
    have hcv' : ContinuousOn
        (fun t : ℝ ↦ iteratedFDeriv ℝ (n + 1 + 1) f (x + t • y) (fun _ ↦ y))
        (Set.uIcc 0 1) := hcont (n + 1) hf
    have hint1 : IntervalIntegrable (fun t : ℝ ↦ (1 - t) ^ (n + 1) •
        iteratedFDeriv ℝ (n + 1 + 1) f (x + t • y) (fun _ ↦ y)) MeasureTheory.volume 0 1 :=
      (hcu.continuousOn.smul hcv').intervalIntegrable
    have hint2 : IntervalIntegrable (fun t : ℝ ↦ (-(((n : ℝ) + 1) * (1 - t) ^ n)) •
        iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y)) MeasureTheory.volume 0 1 :=
      (hcu'.continuousOn.smul hcv).intervalIntegrable
    have hIBP0 : ∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) •
          iteratedFDeriv ℝ (n + 1 + 1) f (x + t • y) (fun _ ↦ y)
        = ((1 : ℝ) - 1) ^ (n + 1) • iteratedFDeriv ℝ (n + 1) f (x + (1 : ℝ) • y) (fun _ ↦ y)
          - ((1 : ℝ) - 0) ^ (n + 1) • iteratedFDeriv ℝ (n + 1) f (x + (0 : ℝ) • y) (fun _ ↦ y)
          - ∫ t in (0 : ℝ)..1, (-(((n : ℝ) + 1) * (1 - t) ^ n)) •
            iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht ↦ (hu t ht).smul (hv t ht)) (hint1.add hint2)
      rw [intervalIntegral.integral_add hint1 hint2] at hFTC
      exact eq_sub_of_add_eq hFTC
    have e1 : ((1 : ℝ) - 1) ^ (n + 1) = 0 := by simp
    have e2 : ((1 : ℝ) - 0) ^ (n + 1) = 1 := by simp
    have e3 : x + (0 : ℝ) • y = x := by simp
    have e4 : ∫ t in (0 : ℝ)..1, (-(((n : ℝ) + 1) * (1 - t) ^ n)) •
          iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y)
        = -(((n : ℝ) + 1) • ∫ t in (0 : ℝ)..1, (1 - t) ^ n •
          iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y)) := by
      first
        | simp only [neg_smul, mul_smul, intervalIntegral.integral_neg,
            intervalIntegral.integral_smul]
        | simp [neg_smul, mul_smul, intervalIntegral.integral_neg, intervalIntegral.integral_smul]
    rw [e1, e2, zero_smul, one_smul, e3, e4] at hIBP0
    have hb : (((n + 1)! : ℕ) : ℝ)⁻¹ * ((n : ℝ) + 1) = ((n ! : ℕ) : ℝ)⁻¹ := by
      have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
      first
        | rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, mul_inv, mul_comm, ← mul_assoc,
            mul_inv_cancel₀ h2, one_mul]
        | (rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
           field_simp)
    rw [ih hf', Finset.sum_range_succ _ (n + 1), add_assoc]
    congr 1
    rw [hIBP0, smul_sub, smul_sub, smul_zero, smul_neg, smul_smul, hb]
    abel
