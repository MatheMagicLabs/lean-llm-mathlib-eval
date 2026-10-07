/-
Machine-generated proof, verified by Lean.

Theorem:      exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Integral/IntervalIntegral/MeanValue.lean, line 115
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  44 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (hab : a ≤ b) (hf : 0 ≤ f b) (hf_mon : AntitoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) :
    ∃ ξ ∈ Icc a b, ∫ x in a..b, f x * g x = f a * ∫ x in a..ξ, g x := by
  obtain ⟨φ, hφ_eq, hφ_anti, hφ_nonneg, hφ_le⟩ : ∃ φ : ℝ → ℝ, (∀ x ∈ Icc a b, φ x = f x) ∧
      Antitone φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ f a) := by
    have hproj_mem : ∀ x, max a (min b x) ∈ Icc a b := fun x =>
      ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
    refine ⟨fun x => f (max a (min b x)), ?_, ?_, ?_, ?_⟩
    · intro x hx
      show f (max a (min b x)) = f x
      rw [min_eq_right hx.2, max_eq_right hx.1]
    · intro x y hxy
      have h1 : max a (min b x) ≤ max a (min b y) := by
        first
        | exact max_le_max le_rfl (min_le_min le_rfl hxy)
        | exact max_le_max_left _ (min_le_min_left _ hxy)
        | gcongr
      exact hf_mon (hproj_mem x) (hproj_mem y) h1
    · intro x
      exact hf.trans (hf_mon (hproj_mem x) (right_mem_Icc.2 hab) (hproj_mem x).2)
    · intro x
      exact hf_mon (left_mem_Icc.2 hab) (hproj_mem x) (hproj_mem x).1
  have hφ_meas : Measurable φ := hφ_anti.measurable
  have htransfer : ∫ x in a..b, f x * g x = ∫ x in a..b, φ x * g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp only [hφ_eq x hx]
  have hA0 : 0 ≤ f a := hf.trans (hf_mon (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab)
  rcases hA0.eq_or_lt with hA | hA
  · refine ⟨a, left_mem_Icc.2 hab, ?_⟩
    rw [← hA, zero_mul, htransfer]
    have h0 : ∀ x, φ x = 0 := fun x =>
      le_antisymm (by rw [hA]; exact hφ_le x) (hφ_nonneg x)
    simp [h0]
  have hA' : f a ≠ 0 := hA.ne'
  have hGcont : ContinuousOn (fun ξ => ∫ x in a..ξ, g x) (Icc a b) := by
    first
    | (have h := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc; rwa [uIcc_of_le hab] at h)
    | (have h := intervalIntegral.continuousOn_primitive_interval (intervalIntegrable_iff'.mp hg); rwa [uIcc_of_le hab] at h)
  obtain ⟨ξmin, hξmin, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hGcont
  obtain ⟨ξmax, hξmax, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hGcont
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (f a))) := by
    first
    | infer_instance
    | exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    | exact ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hKset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ φ p.1} :=
    measurableSet_le measurable_snd (hφ_meas.comp measurable_fst)
  have hgprod : Integrable (fun p : ℝ × ℝ => g p.1)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 (f a)))) := by
    have hg1 : Integrable g (volume.restrict (Ioc a b)) := hg.1
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 (f a))) :=
      MeasureTheory.integrable_const _
    first
    | (have h := hg1.prod_mul h1; simpa using h)
    | exact hg1.comp_fst _
    | (have h := hg1.prod_smul h1; simpa using h)
  have hKint : Integrable (Function.uncurry fun x r =>
      {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 (f a)))) := by
    first
    | exact hgprod.indicator hKset
    | (convert hgprod.indicator hKset using 1; funext p; rfl)
  have hlayer : ∀ x, ∫ r in Ioc 0 (f a),
      {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) = φ x * g x := by
    intro x
    have h1 : ∀ r, {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) =
        (Iic (φ x)).indicator (fun _ => g x) r := fun r => by
      first
      | rfl
      | simp [Set.indicator_apply]
    have hset : Ioc 0 (f a) ∩ Iic (φ x) = Ioc 0 (φ x) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans (hφ_le x)⟩, h2⟩
    simp only [h1]
    first
    | rw [MeasureTheory.setIntegral_indicator measurableSet_Iic, hset]
    | rw [MeasureTheory.integral_indicator measurableSet_Iic,
        Measure.restrict_restrict measurableSet_Iic, Set.inter_comm, hset]
    rw [← intervalIntegral.integral_of_le (hφ_nonneg x), intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
  have hH : ∀ r, ∃ c ∈ Icc a b, ∫ x in Ioc a b,
      {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) = ∫ x in a..c, g x := by
    intro r
    have h1 : ∀ x, {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) =
        {x | r ≤ φ x}.indicator g x := fun x => by
      first
      | rfl
      | simp [Set.indicator_apply]
    simp only [h1]
    have hmr : MeasurableSet {x | r ≤ φ x} := measurableSet_le measurable_const hφ_meas
    have hTne : (insert a {x | x ∈ Icc a b ∧ r ≤ φ x}).Nonempty := ⟨a, Set.mem_insert _ _⟩
    have hTbdd : BddAbove (insert a {x | x ∈ Icc a b ∧ r ≤ φ x}) := by
      refine ⟨b, ?_⟩
      rintro x (rfl | ⟨hx, _⟩)
      · exact hab
      · exact hx.2
    have hac : a ≤ sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x}) :=
      le_csSup hTbdd (Set.mem_insert _ _)
    refine ⟨sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x}), ⟨hac, csSup_le hTne ?_⟩, ?_⟩
    · rintro x (rfl | ⟨hx, _⟩)
      · exact hab
      · exact hx.2
    first
    | rw [MeasureTheory.setIntegral_indicator hmr]
    | rw [MeasureTheory.integral_indicator hmr, Measure.restrict_restrict hmr, Set.inter_comm]
    rw [intervalIntegral.integral_of_le hac]
    have hsub1 : Ioc a b ∩ {x | r ≤ φ x} ⊆
        Ioc a (sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x})) := by
      rintro x ⟨⟨hax, hxb⟩, hrx⟩
      exact ⟨hax, le_csSup hTbdd (Set.mem_insert_of_mem _ ⟨⟨hax.le, hxb⟩, hrx⟩)⟩
    have hsub2 : Ioo a (sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x})) ⊆
        Ioc a b ∩ {x | r ≤ φ x} := by
      rintro x ⟨hax, hxc⟩
      obtain ⟨y, hyT, hxy⟩ := exists_lt_of_lt_csSup hTne hxc
      rcases hyT with rfl | ⟨hy, hry⟩
      · exact (lt_asymm hax hxy).elim
      · exact ⟨⟨hax, hxy.le.trans hy.2⟩, hry.trans (hφ_anti hxy.le)⟩
    have hae : Ioc a b ∩ {x | r ≤ φ x} =ᵐ[volume]
        Ioc a (sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x})) := by
      have h3 : Ioc a (sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x})) =ᵐ[volume]
          Ioo a (sSup (insert a {x | x ∈ Icc a b ∧ r ≤ φ x})) := Ioo_ae_eq_Ioc.symm
      exact (HasSubset.Subset.eventuallyLE hsub1).antisymm
        (h3.le.trans (HasSubset.Subset.eventuallyLE hsub2))
    first
    | exact MeasureTheory.setIntegral_congr_set hae
    | exact MeasureTheory.setIntegral_congr_set_ae hae
  have hfub : ∫ x in a..b, φ x * g x = ∫ r in Ioc 0 (f a),
      ∫ x in Ioc a b, {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) := by
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_integral_swap hKint]
    simp only [hlayer]
  have hHint : Integrable (fun r => ∫ x in Ioc a b,
      {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r))
      (volume.restrict (Ioc 0 (f a))) := by
    first
    | exact hKint.integral_prod_right
    | exact hKint.integral_prod_left
  have hbounds : ∀ r, (∫ x in a..ξmin, g x) ≤ ∫ x in Ioc a b,
        {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) ∧
      ∫ x in Ioc a b, {p : ℝ × ℝ | p.2 ≤ φ p.1}.indicator (fun p => g p.1) (x, r) ≤
        ∫ x in a..ξmax, g x := by
    intro r
    obtain ⟨c, hc, hHc⟩ := hH r
    rw [hHc]
    exact ⟨isMinOn_iff.mp hmin c hc, isMaxOn_iff.mp hmax c hc⟩
  have hconst : ∀ c : ℝ, ∫ _ in Ioc 0 (f a), c = c * f a := by
    intro c
    rw [← intervalIntegral.integral_of_le hA.le, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_comm]
  have hlow : (∫ x in a..ξmin, g x) * f a ≤ ∫ x in a..b, φ x * g x := by
    rw [hfub, ← hconst]
    exact MeasureTheory.integral_mono (MeasureTheory.integrable_const _) hHint
      (fun r => (hbounds r).1)
  have hup : ∫ x in a..b, φ x * g x ≤ (∫ x in a..ξmax, g x) * f a := by
    rw [hfub, ← hconst]
    exact MeasureTheory.integral_mono hHint (MeasureTheory.integrable_const _)
      (fun r => (hbounds r).2)
  have hy_mem : (∫ x in a..b, φ x * g x) / f a ∈
      Icc (∫ x in a..ξmin, g x) (∫ x in a..ξmax, g x) := by
    constructor
    · first
      | exact (le_div_iff₀ hA).2 hlow
      | exact (le_div_iff hA).2 hlow
    · first
      | exact (div_le_iff₀ hA).2 hup
      | exact (div_le_iff hA).2 hup
  have hsub : uIcc ξmin ξmax ⊆ Icc a b := uIcc_subset_Icc hξmin hξmax
  obtain ⟨ξ, hξ, hGξ⟩ := intermediate_value_uIcc (hGcont.mono hsub) (Icc_subset_uIcc hy_mem)
  refine ⟨ξ, hsub hξ, ?_⟩
  have hGξ' : ∫ x in a..ξ, g x = (∫ x in a..b, φ x * g x) / f a := hGξ
  rw [htransfer, hGξ']
  first
  | (field_simp; done)
  | rw [mul_div_assoc', mul_div_cancel_left₀ _ hA']
  | (field_simp; ring)
