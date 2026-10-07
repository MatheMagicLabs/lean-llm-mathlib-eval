/-
Machine-generated proof, verified by Lean.

Theorem:      Manifold.IsSubmersionAtOfComplement.trans_F
Source:       Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/Submersion.lean, line 319
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Geometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma trans_F (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F' I J n f x := by
  first
    | refine IsSubmersionAtOfComplement.mk_of_charts
          (h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e))
          h.domChart h.codChart h.mem_domChart_source h.mem_codChart_source
          h.domChart_mem_maximalAtlas h.codChart_mem_maximalAtlas
          h.source_subset_preimage_source ?_
    | refine IsSubmersionAtOfComplement.mk_of_charts
          (h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prod e))
          h.domChart h.codChart h.mem_domChart_source h.mem_codChart_source
          h.domChart_mem_maximalAtlas h.codChart_mem_maximalAtlas
          h.source_subset_preimage_source ?_
  intro y hy
  first
    | simpa using h.writtenInCharts hy
    | exact h.writtenInCharts hy
    | (rw [Function.comp_apply, Function.comp_apply, ContinuousLinearEquiv.trans_apply]
       exact h.writtenInCharts hy)
