/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.integral_continuousLinearMap_comp
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean, line 386
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  25 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem integral_continuousLinearMap_comp
    {f : X → H} {C : H →L[ℝ] E} (hf : Integrable f μ.variation) :
    ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ] := by
  by_cases hG : CompleteSpace G; swap
  · first
    | simp [VectorMeasure.integral, hG]
    | simp [integral, hG]
    | simp [VectorMeasure.integral_def, hG]
    | rw [integral_of_not_completeSpace hG, integral_of_not_completeSpace hG]
    | simp [integral_of_not_completeSpace hG]
    | simp [hG]
  apply hf.induction (P := fun f ↦ ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    have A : ∀ y, C (s.indicator (fun _ ↦ c) y) = s.indicator (fun _ ↦ C c) y := by
      intro y
      by_cases hy : y ∈ s
      · first
        | simp [hy]
        | simp [hy, Set.indicator_apply]
      · first
        | simp [hy]
        | simp [hy, Set.indicator_apply]
    simp only [A]
    rw [integral_indicator_const _ hs, integral_indicator_const _ hs]
    try (first | rfl | simp)
  · intro f g _ f_int g_int hf hg
    have Cf : Integrable (fun y ↦ C (f y)) μ.variation := C.integrable_comp f_int
    have Cg : Integrable (fun y ↦ C (g y)) μ.variation := C.integrable_comp g_int
    simp only [Pi.add_apply, map_add]
    first
    | rw [integral_fun_add Cf Cg, integral_fun_add f_int g_int, hf, hg]
    | simp [integral_fun_add, Cf, Cg, f_int, g_int, hf, hg]
  · apply isClosed_eq
    · have h1 : Continuous (fun f : X →₁[μ.variation] H ↦
          ∫ᵛ y, (C.compLpL 1 μ.variation f) y ∂[B; μ]) :=
        continuous_integral.comp (C.compLpL 1 μ.variation).continuous
      refine h1.congr (fun f ↦ ?_)
      apply integral_congr_ae
      filter_upwards [C.coeFn_compLp f] with y hy
      first
      | exact hy
      | (rw [ContinuousLinearMap.coe_compLpL]; exact hy)
      | simpa [ContinuousLinearMap.coe_compLpL] using hy
    · exact continuous_integral
  · intro f g hfg _ hf
    have hCfg : (fun y ↦ C (f y)) =ᵐ[μ.variation] (fun y ↦ C (g y)) := by
      filter_upwards [hfg] with y hy
      rw [hy]
    rw [← integral_congr_ae hCfg, ← integral_congr_ae hfg, hf]
