/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion_nat
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean, line 471
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  34 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private theorem hasSum_setIntegral_iUnion_nat {s : ℕ → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG, hasSum_zero]
  have hU : MeasurableSet (⋃ i, s i) := MeasurableSet.iUnion hm
  have hfi' : Integrable f (μ.variation.restrict (⋃ i, s i)) := by
    first
    | have h0 : Integrable f (μ.restrict (⋃ i, s i)).variation := hfi
      rwa [variation_restrict hU] at h0
    | simpa [VectorMeasure.IntegrableOn, variation_restrict hU] using hfi
  have hsub : ∀ t : Finset ℕ, (⋃ n ∈ t, s n) ⊆ ⋃ i, s i := by
    intro t x hx
    obtain ⟨k, _, hxk⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion.2 ⟨k, hxk⟩
  have hint : ∀ n, Integrable ((s n).indicator f) μ.variation := fun n ↦
    MeasureTheory.IntegrableOn.integrable_indicator
      (hfi'.mono_measure (Measure.restrict_mono (subset_iUnion s n) le_rfl)) (hm n)
  have hint' : ∀ t : Finset ℕ, Integrable ((⋃ n ∈ t, s n).indicator f) μ.variation := fun t ↦
    MeasureTheory.IntegrableOn.integrable_indicator
      (hfi'.mono_measure (Measure.restrict_mono (hsub t) le_rfl))
      (Finset.measurableSet_biUnion t (fun n _ ↦ hm n))
  have hintU : Integrable ((⋃ i, s i).indicator f) μ.variation :=
    MeasureTheory.IntegrableOn.integrable_indicator hfi' hU
  have A : ∀ t : Finset ℕ, ∑ n ∈ t, ∫ᵛ x in s n, f x ∂[B; μ] =
      ∫ᵛ x, (⋃ n ∈ t, s n).indicator f x ∂[B; μ] := by
    intro t
    have e1 : ∀ n, ∫ᵛ x in s n, f x ∂[B; μ] = ∫ᵛ x, (s n).indicator f x ∂[B; μ] :=
      fun n ↦ (integral_indicator (hm n)).symm
    have e2 : ∀ x, (⋃ n ∈ t, s n).indicator f x = ∑ n ∈ t, (s n).indicator f x := by
      intro x
      by_cases hx : ∃ k ∈ t, x ∈ s k
      · obtain ⟨k, hkt, hxk⟩ := hx
        have hxU : x ∈ ⋃ n ∈ t, s n := Set.mem_iUnion₂.2 ⟨k, hkt, hxk⟩
        rw [Set.indicator_of_mem hxU, Finset.sum_eq_single_of_mem k hkt,
          Set.indicator_of_mem hxk]
        intro n _ hnk
        exact Set.indicator_of_notMem (fun h ↦ Set.disjoint_left.1 (hd hnk) h hxk) _
      · have hxU : x ∉ ⋃ n ∈ t, s n := by
          intro h
          obtain ⟨k, hkt, hxk⟩ := Set.mem_iUnion₂.1 h
          exact hx ⟨k, hkt, hxk⟩
        rw [Set.indicator_of_notMem hxU]
        exact (Finset.sum_eq_zero
          (fun n hn ↦ Set.indicator_of_notMem (fun h ↦ hx ⟨n, hn, h⟩) _)).symm
    simp_rw [e1, e2]
    rw [integral_finsetSum _ (fun n _ ↦ hint n)]
  simp only [HasSum, SummationFilter.unconditional_filter]
  simp_rw [A]
  rw [← integral_indicator hU]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x ↦ ‖(⋃ i, s i).indicator f x‖)
  · exact Eventually.of_forall (fun t ↦ (hint' t).aestronglyMeasurable)
  · filter_upwards with t
    filter_upwards with x
    first
    | exact norm_indicator_le_of_subset (hsub t) f x
    | by_cases hx : x ∈ ⋃ n ∈ t, s n
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub t hx)]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
  · exact hintU.norm
  · filter_upwards with x
    by_cases hx : x ∈ ⋃ i, s i
    · obtain ⟨k, hxk⟩ := Set.mem_iUnion.1 hx
      rw [Set.indicator_of_mem hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop ({k} : Finset ℕ)] with t ht
      have hxt : x ∈ ⋃ n ∈ t, s n :=
        Set.mem_iUnion₂.2 ⟨k, Finset.singleton_subset_iff.1 ht, hxk⟩
      exact (Set.indicator_of_mem hxt f).symm
    · rw [Set.indicator_of_notMem hx]
      apply tendsto_const_nhds.congr'
      filter_upwards with t
      exact (Set.indicator_of_notMem (fun h ↦ hx (hsub t h)) f).symm
