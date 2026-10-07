/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.integral_prod
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Prod.lean, line 314
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  31 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem integral_prod {B : G →L[ℝ] F →L[ℝ] J} {C : J →L[ℝ] E →L[ℝ] I}
    {A : E →L[ℝ] F →L[ℝ] H} {D : G →L[ℝ] H →L[ℝ] I}
    [CompleteSpace H] [CompleteSpace J]
    [IsFiniteMeasure ν.variation] [IsFiniteMeasure μ.variation]
    {f : X × Y → G} (hf : Integrable f (μ.variation.prod ν.variation))
    (h : ∀ x y z, D x (A y z) = C (B x z) y) :
    ∫ᵛ z, f z ∂[D; μ.prod ν A] = ∫ᵛ x, (∫ᵛ y, f (x, y) ∂[B; ν]) ∂[C; μ] := by
  by_cases hI : CompleteSpace I; swap
  · simp [integral_of_not_completeSpace hI]
  apply hf.induction (P := fun f ↦
    ∫ᵛ z, f z ∂[D; μ.prod ν A] = ∫ᵛ x, (∫ᵛ y, f (x, y) ∂[B; ν]) ∂[C; μ])
  · intro c s hs _
    have hint : Integrable (fun x ↦ ν (Prod.mk x ⁻¹' s)) μ.variation :=
      integrable_vectorMeasure_prodMk_left hs
    have e : ∀ x, ∫ᵛ y, s.indicator (fun _ ↦ c) (x, y) ∂[B; ν] = B c (ν (Prod.mk x ⁻¹' s)) := by
      intro x
      have : (fun y ↦ s.indicator (fun _ ↦ c) (x, y)) =
          (Prod.mk x ⁻¹' s).indicator (fun _ ↦ c) := by
        ext y
        first
        | rfl
        | simp [Set.indicator_apply]
      rw [this, integral_indicator_const c (measurable_prodMk_left hs)]
    simp_rw [e]
    rw [integral_indicator_const c hs, prod_apply_eq_integral hs,
      continuousLinearMap_apply_integral hint, integral_continuousLinearMap_comp hint]
    congr 1
    ext v w
    first
    | (simp [h]; done)
    | exact h c w v
    | (simp [ContinuousLinearMap.compL_apply]; exact h c w v)
  · intro f g _ f_int g_int hf hg
    have i1 : (fun x ↦ ∫ᵛ y, (f + g) (x, y) ∂[B; ν]) =ᵐ[μ.variation]
        fun x ↦ ∫ᵛ y, f (x, y) ∂[B; ν] + ∫ᵛ y, g (x, y) ∂[B; ν] := by
      filter_upwards [f_int.prod_right_ae, g_int.prod_right_ae] with x hfx hgx
      exact integral_fun_add hfx hgx
    rw [integral_congr_ae i1, integral_fun_add (f_int.integral_vectorMeasure_prod_left (B := B))
      (g_int.integral_vectorMeasure_prod_left (B := B)), ← hf, ← hg]
    exact integral_fun_add (f_int.prod_vectorMeasure (B := A)) (g_int.prod_vectorMeasure (B := A))
  · apply isClosed_eq
    · apply continuous_iff_continuousAt.2 (fun g ↦ ?_)
      apply tendsto_integral_of_L1
      · first
        | exact MeasureTheory.Integrable.aestronglyMeasurable ((L1.integrable_coeFn g).prod_vectorMeasure (B := A))
        | exact (L1.integrable_coeFn g).prod_vectorMeasure (B := A)
      · filter_upwards with i
        exact (L1.integrable_coeFn i).prod_vectorMeasure (B := A)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i ↦ zero_le) _
        (h := fun i ↦ ‖A‖ₑ * ∫⁻ z, ‖i z - g z‖ₑ ∂(μ.variation.prod ν.variation)); swap
      · intro i
        refine (lintegral_mono' (variation_prod_le (μ := μ) (ν := ν) (B := A)) le_rfl).trans
          (le_of_eq ?_)
        simp [lintegral_smul_measure]
      simp_rw [← L1.ofReal_norm_sub_eq_lintegral, ofReal_norm]
      suffices Tendsto (fun i ↦ ‖A‖ₑ * ‖i - g‖ₑ) (𝓝 g) (𝓝 (‖A‖ₑ * 0)) by simpa
      apply ENNReal.Tendsto.const_mul _ (by simp)
      rw [← tendsto_iff_enorm_sub_tendsto_zero]
      exact tendsto_id
    · exact continuous_integral_integral
  · intro f g hfg _ hf
    have h1 : f =ᵐ[(μ.prod ν A).variation] g := by
      first
      | exact (Measure.absolutelyContinuous_of_le_smul
          (variation_prod_le (μ := μ) (ν := ν) (B := A))).ae_eq hfg
      | exact MeasureTheory.ae_mono (variation_prod_le (μ := μ) (ν := ν) (B := A))
          (ae_smul_measure hfg _)
    have h2 : (fun x ↦ ∫ᵛ y, f (x, y) ∂[B; ν]) =ᵐ[μ.variation]
        fun x ↦ ∫ᵛ y, g (x, y) ∂[B; ν] := by
      filter_upwards [Measure.ae_ae_of_ae_prod hfg] with x hx using integral_congr_ae hx
    rw [← integral_congr_ae h1, ← integral_congr_ae h2]
    exact hf
