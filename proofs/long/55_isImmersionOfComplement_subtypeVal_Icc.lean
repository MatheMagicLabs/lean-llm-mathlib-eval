/-
Machine-generated proof, verified by Lean.

Theorem:      isImmersionOfComplement_subtypeVal_Icc
Source:       Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/Instances/Icc.lean, line 72
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  31 tactic steps; area: Geometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma isImmersionOfComplement_subtypeVal_Icc :
    IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  obtain ⟨L, hL⟩ : ∃ L : (EuclideanSpace ℝ (Fin 1) × Unit) ≃L[ℝ] ℝ,
      ∀ u : EuclideanSpace ℝ (Fin 1), L (u, 0) = u 0 := by
    first
      | exact ⟨(ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) Unit).trans ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)), fun u => by first | rfl | simp⟩
      | exact ⟨(ContinuousLinearEquiv.prodUnique : (EuclideanSpace ℝ (Fin 1) × Unit) ≃L[ℝ] EuclideanSpace ℝ (Fin 1)).trans ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)), fun u => by first | rfl | simp⟩
      | exact ⟨(LinearEquiv.prodUnique : (EuclideanSpace ℝ (Fin 1) × Unit) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).toContinuousLinearEquiv.trans ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)), fun u => by first | rfl | simp⟩
  have hψ : ∀ c : ℝ, (Homeomorph.addRight c).toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ) n ℝ := by
    intro c
    apply StructureGroupoid.mem_maximalAtlas_of_mem_groupoid
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    constructor
    · apply ContDiff.contDiffOn
      first
        | (show ContDiff ℝ n (fun t : ℝ => t + c); fun_prop)
        | (simp; fun_prop)
    · apply ContDiff.contDiffOn
      first
        | (show ContDiff ℝ n (fun t : ℝ => t + -c); fun_prop)
        | (show ContDiff ℝ n (fun t : ℝ => t - c); fun_prop)
        | (simp; fun_prop)
  by_cases hz : (z : ℝ) < y
  · have hdom : IccLeftChart x y ∈ IsManifold.maximalAtlas (𝓡∂ 1) n (Icc x y) := by
      first
        | exact IsManifold.subset_maximalAtlas (Set.mem_insert _ _)
        | exact IsManifold.subset_maximalAtlas (by simp [atlas])
        | (have := IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ 1) (n := n) z; simpa [hz] using this)
    have hEq : Set.EqOn (((Homeomorph.addRight (-x)).toOpenPartialHomeomorph.extend 𝓘(ℝ)) ∘
        (fun z : Icc x y => (z : ℝ)) ∘ ((IccLeftChart x y).extend (𝓡∂ 1)).symm) (L ∘ (·, 0))
        ((IccLeftChart x y).extend (𝓡∂ 1)).target := by
      intro u hu
      have hu' := ((IccLeftChart x y).extend (𝓡∂ 1)).right_inv hu
      have e1 : u 0 = (((IccLeftChart x y).extend (𝓡∂ 1))
          (((IccLeftChart x y).extend (𝓡∂ 1)).symm u)) 0 := by
        rw [hu']
      have hu0 : u 0 = ((((IccLeftChart x y).extend (𝓡∂ 1)).symm u : Icc x y) : ℝ) - x :=
        e1.trans rfl
      show ((((IccLeftChart x y).extend (𝓡∂ 1)).symm u : Icc x y) : ℝ) + -x = L (u, 0)
      rw [hL, hu0]
      ring
    first
      | (refine IsImmersionAtOfComplement.mk_of_charts L (IccLeftChart x y)
            (Homeomorph.addRight (-x)).toOpenPartialHomeomorph ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first | exact hEq | exact hz | exact Set.mem_univ _ | exact hdom | exact hψ (-x) | exact fun _ _ => Set.mem_univ _)
      | (refine IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt L
            (IccLeftChart x y) (Homeomorph.addRight (-x)).toOpenPartialHomeomorph ?_ ?_ ?_ ?_ ?_ <;>
          first | exact hEq | exact hz | exact Set.mem_univ _ | exact hdom | exact hψ (-x) | exact fun _ _ => Set.mem_univ _)
      | (rw [IsImmersionAtOfComplement_def]; exact ⟨⟨IccLeftChart x y, (Homeomorph.addRight (-x)).toOpenPartialHomeomorph, hz, Set.mem_univ _, hdom, hψ (-x), fun _ _ => Set.mem_univ _, L, hEq⟩⟩)
  · have hz' : x < (z : ℝ) := lt_of_lt_of_le (Fact.out : x < y) (not_lt.mp hz)
    have hdom : IccRightChart x y ∈ IsManifold.maximalAtlas (𝓡∂ 1) n (Icc x y) := by
      first
        | exact IsManifold.subset_maximalAtlas (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        | exact IsManifold.subset_maximalAtlas (by simp [atlas])
        | (have := IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ 1) (n := n) z; simpa [hz] using this)
    have hEq : Set.EqOn (((Homeomorph.addRight (-y)).toOpenPartialHomeomorph.extend 𝓘(ℝ)) ∘
        (fun z : Icc x y => (z : ℝ)) ∘ ((IccRightChart x y).extend (𝓡∂ 1)).symm)
        ((L.trans (ContinuousLinearEquiv.neg ℝ)) ∘ (·, 0))
        ((IccRightChart x y).extend (𝓡∂ 1)).target := by
      intro u hu
      have hu' := ((IccRightChart x y).extend (𝓡∂ 1)).right_inv hu
      have e1 : u 0 = (((IccRightChart x y).extend (𝓡∂ 1))
          (((IccRightChart x y).extend (𝓡∂ 1)).symm u)) 0 := by
        rw [hu']
      have hu0 : u 0 = y - ((((IccRightChart x y).extend (𝓡∂ 1)).symm u : Icc x y) : ℝ) :=
        e1.trans rfl
      show ((((IccRightChart x y).extend (𝓡∂ 1)).symm u : Icc x y) : ℝ) + -y = -(L (u, 0))
      rw [hL, hu0]
      ring
    first
      | (refine IsImmersionAtOfComplement.mk_of_charts (L.trans (ContinuousLinearEquiv.neg ℝ))
            (IccRightChart x y) (Homeomorph.addRight (-y)).toOpenPartialHomeomorph ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first | exact hEq | exact hz' | exact Set.mem_univ _ | exact hdom | exact hψ (-y) | exact fun _ _ => Set.mem_univ _)
      | (refine IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt
            (L.trans (ContinuousLinearEquiv.neg ℝ)) (IccRightChart x y)
            (Homeomorph.addRight (-y)).toOpenPartialHomeomorph ?_ ?_ ?_ ?_ ?_ <;>
          first | exact hEq | exact hz' | exact Set.mem_univ _ | exact hdom | exact hψ (-y) | exact fun _ _ => Set.mem_univ _)
      | (rw [IsImmersionAtOfComplement_def]; exact ⟨⟨IccRightChart x y, (Homeomorph.addRight (-y)).toOpenPartialHomeomorph, hz', Set.mem_univ _, hdom, hψ (-y), fun _ _ => Set.mem_univ _, L.trans (ContinuousLinearEquiv.neg ℝ), hEq⟩⟩)
