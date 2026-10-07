/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSpace/InfiniteSum.lean, line 30
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  58 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem summable_norm_of_tsum_eLpNorm_ne_top {ι : Type*} [Countable ι]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → X → E} (h'f : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    ∀ᵐ a ∂μ, Summable (fun n ↦ ‖f n a‖) := by
  classical
  have hfin : ∀ n, eLpNorm (f n) p μ ≠ ∞ := fun n => ENNReal.ne_top_of_tsum_ne_top h'f n
  have hmeas : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    by_contra hn
    exact hfin n (eLpNorm_of_not_aestronglyMeasurable hn)
  have key : ∀ᵐ a ∂μ, ∑' n, ‖f n a‖ₑ ≠ ∞ := by
    by_cases hp_top : p = ∞
    · have H : ∀ n, ∀ᵐ a ∂μ, ‖f n a‖ₑ ≤ eLpNorm (f n) p μ := by
        intro n
        rw [hp_top]
        first
          | rw [eLpNorm_exponent_top (hmeas n)]
          | rw [eLpNorm_exponent_top]
        exact enorm_ae_le_eLpNormEssSup (f n) μ
      filter_upwards [ae_all_iff.mpr H] with a ha
      first
        | exact ne_top_of_le_ne_top h'f (ENNReal.tsum_le_tsum ha)
        | exact ne_top_of_le_ne_top h'f (ENNReal.tsum_mono ha)
    · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
      have hq1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
      have hq0 : 0 < p.toReal := zero_lt_one.trans_le hq1
      have hLp : ∀ n, eLpNorm (f n) p μ
          = (∫⁻ a, ‖f n a‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        intro n
        first
          | (rw [eLpNorm_eq_eLpNorm' hp0 hp_top (hmeas n), eLpNorm'_eq_lintegral_enorm]; done)
          | exact eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top
          | exact eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top (hmeas n)
      have hsum : ∀ s : Finset ι, AEMeasurable (fun a => ∑ n ∈ s, ‖f n a‖ₑ) μ := by
        intro s
        first
          | exact Finset.aemeasurable_sum s (fun n _ => (hmeas n).enorm)
          | exact Finset.aemeasurable_fun_sum s (fun n _ => (hmeas n).enorm)
          | (refine Finset.induction_on s ?_ ?_
             · simp
             · intro i s hi ih
               simp only [Finset.sum_insert hi]
               exact (hmeas i).enorm.add ih)
      have hmin : ∀ s : Finset ι, (∫⁻ a, (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal ∂μ) ^ (1 / p.toReal)
          ≤ ∑ n ∈ s, eLpNorm (f n) p μ := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos hq0, lintegral_zero]
          first
            | exact (ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq0)).le
            | simp [hq0]
        · intro i s hi ih
          simp only [Finset.sum_insert hi]
          refine (ENNReal.lintegral_Lp_add_le (hmeas i).enorm (hsum s) hq1).trans ?_
          exact add_le_add (hLp i).ge ih
      have hstep : ∀ s : Finset ι, ∫⁻ a, (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal ∂μ
          ≤ (∑' n, eLpNorm (f n) p μ) ^ p.toReal := by
        intro s
        have h0 := (hmin s).trans (ENNReal.sum_le_tsum s)
        first
          | exact (ENNReal.rpow_one_div_le_iff hq0).mp h0
          | (have h1 := ENNReal.rpow_le_rpow h0 hq0.le
             rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at h1)
      have hΦmeas : ∀ s : Finset ι,
          AEMeasurable (fun a => (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal) μ := by
        intro s
        first
          | exact (hsum s).pow_const _
          | exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hsum s)
      have hdir : Directed (· ≤ ·)
          (fun (s : Finset ι) (a : X) => (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal) := by
        intro s t
        refine ⟨s ∪ t, ?_, ?_⟩
        · intro a
          exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset
            (fun x hx => Finset.mem_union.mpr (Or.inl hx))) hq0.le
        · intro a
          exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset
            (fun x hx => Finset.mem_union.mpr (Or.inr hx))) hq0.le
      have hint : ∫⁻ a, ⨆ s : Finset ι, (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal ∂μ
          ≤ (∑' n, eLpNorm (f n) p μ) ^ p.toReal :=
        (lintegral_iSup_directed hΦmeas hdir).trans_le (iSup_le hstep)
      have hsupmeas : AEMeasurable
          (fun a => ⨆ s : Finset ι, (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal) μ := by
        first
          | exact AEMeasurable.iSup hΦmeas
          | exact aemeasurable_iSup hΦmeas
      have hae := ae_lt_top' hsupmeas
        (ne_top_of_le_ne_top (ENNReal.rpow_lt_top_of_nonneg hq0.le h'f).ne hint)
      filter_upwards [hae] with a ha
      rw [ENNReal.tsum_eq_iSup_sum]
      refine ne_top_of_le_ne_top
        (ENNReal.rpow_lt_top_of_nonneg (one_div_pos.mpr hq0).le ha.ne).ne ?_
      refine iSup_le fun s => ?_
      have hle : (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal
          ≤ ⨆ s : Finset ι, (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal :=
        le_iSup (fun s : Finset ι => (∑ n ∈ s, ‖f n a‖ₑ) ^ p.toReal) s
      first
        | exact (ENNReal.le_rpow_one_div_iff hq0).mpr hle
        | (have h1 := ENNReal.rpow_le_rpow hle (one_div_pos.mpr hq0).le
           rwa [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at h1)
  filter_upwards [key] with a ha
  first
    | simpa using ENNReal.summable_toReal ha
    | exact (ENNReal.summable_toReal ha).congr fun n => toReal_enorm _
