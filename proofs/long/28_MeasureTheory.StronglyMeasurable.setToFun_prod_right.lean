/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.StronglyMeasurable.setToFun_prod_right
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Integral/SetToL1/DominatedConvergence.lean, line 253
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  42 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem StronglyMeasurable.setToFun_prod_right {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    (hT : DominatedFinMeasAdditive μ T C)
    (h'T : ∀ (s : Set (β × α)), MeasurableSet s → StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : β → α → E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable fun x => setToFun μ T hT (f x) := by
  classical
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte]
    exact stronglyMeasurable_const
  borelize E
  have hmk : ∀ x : β, Measurable (Prod.mk x : α → β × α) := fun x => by
    first
      | exact measurable_prodMk_left
      | exact measurable_prod_mk_left
      | fun_prop
  haveI : SeparableSpace (Set.range (Function.uncurry f) ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc (β × α) E :=
    SimpleFunc.approxOn _ hf.measurable (Set.range (Function.uncurry f) ∪ {0}) 0 (by simp)
  let f' : ℕ → β → F := fun n => {x | Integrable (f x) μ}.indicator
    fun x => ∑ y ∈ (s n).range, T (Prod.mk x ⁻¹' (s n ⁻¹' {y})) y
  have hf' : ∀ n, StronglyMeasurable (f' n) := by
    intro n
    refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    have H : ∀ y, StronglyMeasurable fun x => T (Prod.mk x ⁻¹' (s n ⁻¹' {y})) y := by
      intro y
      have h1 := h'T _ ((s n).measurableSet_fiber y)
      first
        | exact h1.apply_continuousLinearMap y
        | exact (ContinuousLinearMap.apply ℝ F y).continuous.comp_stronglyMeasurable h1
        | exact (continuous_eval_const y).comp_stronglyMeasurable h1
    first
      | exact Finset.stronglyMeasurable_fun_sum _ fun y _ => H y
      | exact Finset.stronglyMeasurable_sum _ fun y _ => H y
  have h2f' : Tendsto f' atTop (𝓝 fun x => setToFun μ T hT (f x)) := by
    rw [tendsto_pi_nhds]
    intro x
    by_cases hfx : Integrable (f x) μ
    · have hbound : ∀ n, ∀ᵐ a ∂μ, ‖s n (x, a)‖ ≤ ‖f x a‖ + ‖f x a‖ := fun n =>
        Eventually.of_forall fun a =>
          SimpleFunc.norm_approxOn_zero_le hf.measurable (by simp) (x, a) n
      have hint : ∀ n, Integrable (fun a => s n (x, a)) μ := by
        intro n
        refine (hfx.norm.add hfx.norm).mono' ?_ (hbound n)
        exact ((s n).stronglyMeasurable.comp_measurable (hmk x)).aestronglyMeasurable
      have hlim : ∀ᵐ a ∂μ, Tendsto (fun n => s n (x, a)) atTop (𝓝 (f x a)) := by
        refine Eventually.of_forall fun a => ?_
        have hmem : Function.uncurry f (x, a) ∈
            closure (Set.range (Function.uncurry f) ∪ {0}) :=
          subset_closure (Set.mem_union_left _ (Set.mem_range_self _))
        exact SimpleFunc.tendsto_approxOn hf.measurable (by simp) hmem
      have heq : ∀ n, f' n x = setToFun μ T hT (fun a => s n (x, a)) := by
        intro n
        have hA : ∀ y, MeasurableSet (Prod.mk x ⁻¹' (s n ⁻¹' {y})) := fun y =>
          hmk x ((s n).measurableSet_fiber y)
        have hI : ∀ y, Integrable ((Prod.mk x ⁻¹' (s n ⁻¹' {y})).indicator fun _ => y) μ := by
          intro y
          have hc : ((Prod.mk x ⁻¹' (s n ⁻¹' {y})).indicator fun _ => y) =
              (Prod.mk x ⁻¹' (s n ⁻¹' {y})).indicator (fun a => s n (x, a)) := by
            refine Set.indicator_congr fun a ha => ?_
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
            exact ha.symm
          have hle : ∀ a, ‖(Prod.mk x ⁻¹' (s n ⁻¹' {y})).indicator (fun a => s n (x, a)) a‖
              ≤ ‖s n (x, a)‖ := by
            intro a
            first
              | exact norm_indicator_le_norm_self _ a
              | exact norm_indicator_le_norm_self
              | (rw [Set.indicator_apply]; split_ifs <;> simp)
          have hmeas : AEStronglyMeasurable
              ((Prod.mk x ⁻¹' (s n ⁻¹' {y})).indicator (fun a => s n (x, a))) μ :=
            (((s n).stronglyMeasurable.comp_measurable (hmk x)).indicator
              (hA y)).aestronglyMeasurable
          rw [hc]
          exact (hint n).norm.mono' hmeas (Eventually.of_forall hle)
        have h2 : (fun a => s n (x, a)) = fun a => ∑ y ∈ (s n).range,
            (Prod.mk x ⁻¹' (s n ⁻¹' {y})).indicator (fun _ => y) a := by
          funext a
          rw [Finset.sum_eq_single_of_mem (s n (x, a)) ((s n).mem_range_self (x, a))]
          · simp [Set.indicator_apply]
          · intro y _ hy
            simp [Set.indicator_apply, Ne.symm hy]
        rw [h2, setToFun_finsetSum hT _ (fun y _ => hI y)]
        simp only [f', Set.indicator_of_mem (show x ∈ {x | Integrable (f x) μ} from hfx)]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : y = 0
        · subst hy
          rw [map_zero]
          have h0 : ∀ S : Set α, (S.indicator fun _ => (0 : E)) = 0 := fun S => by
            ext a
            simp
          rw [h0, setToFun_zero]
        · have hint' : Integrable ((s n).comp (Prod.mk x) (hmk x)) μ := by
            first
              | exact hint n
              | (rw [SimpleFunc.coe_comp]; exact hint n)
          have h3 : μ (⇑((s n).comp (Prod.mk x) (hmk x)) ⁻¹' {y}) < ∞ := by
            first
              | exact SimpleFunc.measure_preimage_lt_top_of_integrable _ hint' hy
              | exact SimpleFunc.integrable_iff.mp hint' y hy
          have hμ : μ (Prod.mk x ⁻¹' (s n ⁻¹' {y})) ≠ ∞ := by
            first
              | exact h3.ne
              | (rw [SimpleFunc.coe_comp, Set.preimage_comp] at h3; exact h3.ne)
          first
            | exact (setToFun_indicator_const hT (hA y) hμ y).symm
            | exact (setToFun_indicator_const hT (hA y) hμ.lt_top y).symm
      refine (tendsto_setToFun_of_dominated_convergence hT (fun a => ‖f x a‖ + ‖f x a‖)
        (fun n => (hint n).aestronglyMeasurable) (hfx.norm.add hfx.norm) hbound hlim).congr ?_
      intro n
      exact (heq n).symm
    · have h0 : ∀ n, f' n x = 0 := by
        intro n
        first
          | exact Set.indicator_of_notMem (show x ∉ {x | Integrable (f x) μ} from hfx) _
          | exact Set.indicator_of_not_mem (show x ∉ {x | Integrable (f x) μ} from hfx) _
          | simp [f', hfx]
      simp only [h0, setToFun_undef hT hfx]
      exact tendsto_const_nhds
  exact stronglyMeasurable_of_tendsto _ hf' h2f'
