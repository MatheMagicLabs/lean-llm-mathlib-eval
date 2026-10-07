/-
Machine-generated proof, verified by Lean.

Theorem:      contMDiffAt_localFrameCoeff
Source:       Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/VectorBundle/LocalFrame.lean, line 467
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  12 tactic steps; area: Geometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma contMDiffAt_localFrameCoeff (hxe : x ∈ e.baseSet) (hs : CMDiffAt k (T% s) x) (i : ι) :
    CMDiffAt k ((LinearMap.piApply (e.localFrameCoeff I b i)) s) x := by
  have hg : ContMDiffAt I (modelWithCornersSelf 𝕜 F) k
      (fun y ↦ (e (TotalSpace.mk' F y (s y))).2) x := by
    first
      | exact ((e.contMDiffAt_iff (by first | exact hxe | exact e.mem_source.mpr hxe | simpa using hxe)).mp hs).2
      | (rw [e.contMDiffAt_iff] at hs; exacts [hs.2, e.mem_source.mpr hxe])
      | exact (e.contMDiffAt_section_iff hxe).mp hs
  have h2 : ContMDiffAt I (modelWithCornersSelf 𝕜 𝕜) k
      (⇑(LinearMap.toContinuousLinearMap (b.coord i)) ∘
        fun y ↦ (e (TotalSpace.mk' F y (s y))).2) x := by
    first
      | exact (LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.contMDiffAt.comp x hg
      | exact (LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.comp_contMDiffAt hg
      | exact (LinearMap.toContinuousLinearMap (b.coord i)).contDiff.contMDiff.contMDiffAt.comp x hg
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hxe] with y hy
  first
    | (simp [e.localFrameCoeff_eq_coeff hy]; done)
    | (simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]; rw [← e.localFrameCoeff_eq_coeff hy]; all_goals first | rfl | simp)
