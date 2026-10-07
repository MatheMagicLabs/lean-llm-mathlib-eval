/-
Machine-generated proof, verified by Lean.

Theorem:      Function.locallyFinsuppWithin.finite_support_of_logCounting_isBigO_log
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Asymptotic.lean, line 116
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  28 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma finite_support_of_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) (hO : logCounting D =O[atTop] Real.log) :
    D.support.Finite := by
  classical
  have key : ∀ N : ℕ, ∀ D' : locallyFinsupp E ℤ, 0 ≤ D' → D'.support.Infinite →
      ∃ C : ℝ, ∀ᶠ r in atTop, (N : ℝ) * Real.log r - C ≤ logCounting D' r := by
    intro N
    induction N with
    | zero =>
      intro D' hD' _
      refine ⟨0, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with r hr
      simpa using logCounting_nonneg hD' hr
    | succ n ih =>
      intro D' hD' hinf'
      obtain ⟨e₀, he₀⟩ := hinf'.nonempty
      have hD0 : D' ≠ 0 := by
        rintro rfl
        first
          | exact he₀ rfl
          | exact he₀ (by simp)
      obtain ⟨e, he⟩ := exists_single_le_pos (lt_of_le_of_ne hD' (Ne.symm hD0))
      have h₁ : 0 ≤ D' - single e 1 := sub_nonneg.2 he
      have h₂ : (D' - single e 1).support.Infinite := by
        intro hfin
        apply hinf'
        apply (hfin.union (Set.finite_singleton e)).subset
        intro x hx
        rw [Set.mem_union, Set.mem_singleton_iff]
        by_cases hxe : x = e
        · exact Or.inr hxe
        · left
          have hsx : (single e (1 : ℤ) : locallyFinsupp E ℤ) x = 0 := by
            first
              | (simp [hxe]; done)
              | (simp [single_apply, hxe]; done)
              | (simp [coe_single, hxe]; done)
              | (simp [single_apply, Pi.single_apply, hxe]; done)
              | exact Pi.single_eq_of_ne hxe _
              | exact Pi.single_eq_of_ne' (Ne.symm hxe) _
              | exact if_neg hxe
              | (simp [single, hxe]; done)
              | (simp [single, Pi.single_apply, hxe]; done)
          have hval : (D' - single e (1 : ℤ) : locallyFinsupp E ℤ) x = D' x := by
            first
              | (simp [hsx, hxe]; done)
              | (rw [sub_apply, hsx, sub_zero])
              | (rw [coe_sub, Pi.sub_apply, hsx, sub_zero])
              | (show D' x - (single e (1 : ℤ) : locallyFinsupp E ℤ) x = D' x; rw [hsx, sub_zero])
              | exact (congrArg (D' x - ·) hsx).trans (sub_zero _)
          first
            | (show (D' - single e (1 : ℤ) : locallyFinsupp E ℤ) x ≠ 0; rw [hval]; exact hx)
            | (have hx' : D' x ≠ 0 := hx
               rw [← hval] at hx'
               exact hx')
            | (simpa [hval] using hx)
      obtain ⟨C, hC⟩ := ih (D' - single e 1) h₁ h₂
      refine ⟨C + Real.log ‖e‖, ?_⟩
      filter_upwards [hC, eventually_ge_atTop ‖e‖] with r hr hre
      have hsub : logCounting (D' - single e 1) r =
          logCounting D' r - logCounting (single e 1) r := by
        first
          | (rw [map_sub, Pi.sub_apply])
          | (rw [map_sub]; rfl)
          | simp [map_sub]
      rw [hsub, logCounting_single_eq_log_sub_const hre] at hr
      push_cast at hr ⊢
      have e1 : ((n : ℝ) + 1) * Real.log r = (n : ℝ) * Real.log r + Real.log r := by ring
      linarith
  by_contra hinf
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨C, hC⟩ := key (⌈c⌉₊ + 1) D h hinf
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
    (hc.and (hC.and ((Real.tendsto_log_atTop.eventually_gt_atTop C).and
      (eventually_ge_atTop 1)))).exists
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr4
  have h1 : logCounting D r ≤ c * Real.log r := by
    have h3 : logCounting D r ≤ ‖logCounting D r‖ := by
      first
        | exact Real.le_norm_self _
        | exact (le_abs_self _).trans (Real.norm_eq_abs _).symm.le
    have h4 : ‖Real.log r‖ = Real.log r := by
      first
        | exact Real.norm_of_nonneg hlogr
        | rw [Real.norm_eq_abs, abs_of_nonneg hlogr]
    rw [h4] at hr1
    linarith
  have h2 : c * Real.log r ≤ (⌈c⌉₊ : ℝ) * Real.log r :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil c) hlogr
  push_cast at hr2
  have e2 : ((⌈c⌉₊ : ℝ) + 1) * Real.log r = (⌈c⌉₊ : ℝ) * Real.log r + Real.log r := by ring
  linarith
