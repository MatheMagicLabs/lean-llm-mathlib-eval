/-
Machine-generated proof, verified by Lean.

Theorem:      BoundedVariationOn.variation_vectorMeasure_Ioi
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean, line 453
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  25 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma variation_vectorMeasure_Ioi (hf : BoundedVariationOn f univ) {a : α} :
    hf.vectorMeasure.variation (Ioi a) = eVariationOn f.rightLim (Ioi a) := by
  have : Nonempty α := ⟨a⟩
  apply le_antisymm
  · obtain ⟨u, u_mono, hu⟩ : ∃ u : ℕ → α, Monotone u ∧ Tendsto u atTop atTop :=
      Filter.exists_seq_monotone_tendsto_atTop_atTop α
    have hsub : Ioi a ⊆ ⋃ n, Ioc a (u n) := by
      intro x (hx : a < x)
      obtain ⟨n, hn⟩ := (hu.eventually (eventually_ge_atTop x)).exists
      exact mem_iUnion.2 ⟨n, hx, hn⟩
    have hmono : Monotone (fun n ↦ Ioc a (u n)) :=
      fun i j hij ↦ Ioc_subset_Ioc_right (u_mono hij)
    have hU : hf.vectorMeasure.variation (⋃ n, Ioc a (u n)) =
        ⨆ n, hf.vectorMeasure.variation (Ioc a (u n)) := by
      first
      | exact hmono.measure_iUnion
      | exact hmono.directed_le.measure_iUnion
      | exact measure_iUnion_eq_iSup hmono.directed_le
      | exact tendsto_nhds_unique (tendsto_measure_iUnion_atTop hmono)
          (tendsto_atTop_iSup (fun i j hij ↦ measure_mono (hmono hij)))
    calc hf.vectorMeasure.variation (Ioi a)
    _ ≤ hf.vectorMeasure.variation (⋃ n, Ioc a (u n)) := measure_mono hsub
    _ = ⨆ n, hf.vectorMeasure.variation (Ioc a (u n)) := hU
    _ ≤ eVariationOn f.rightLim (Ioi a) := by
      refine iSup_le fun n ↦ ?_
      rw [hf.variation_vectorMeasure_Ioc]
      first
      | exact eVariationOn.mono _ Ioc_subset_Ioi_self
      | exact eVariationOn.mono _ (fun x hx ↦ hx.1)
      | exact eVariationOn.mono Ioc_subset_Ioi_self
  · simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall, mem_Ioi, and_imp,
      edist_eq_enorm_sub]
    intro n u u_mono u_mem
    calc ∑ i ∈ Finset.range n, ‖Function.rightLim f (u (i + 1)) - Function.rightLim f (u i)‖ₑ
    _ ≤ ∑ i ∈ Finset.range n, hf.vectorMeasure.variation (Ioc (u i) (u (i + 1))) := by
      gcongr with i
      grw [← enorm_measure_le_variation, vectorMeasure_Ioc _ (u_mono (by grind))]
    _ = hf.vectorMeasure.variation (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) := by
      rw [measure_biUnion_finset ?_ (fun i hi ↦ measurableSet_Ioc)]
      rintro i - j - hij
      simp [Function.onFun]
      grind [Monotone]
    _ ≤ hf.vectorMeasure.variation (Ioi a) := by
      apply measure_mono
      intro x hx
      simp only [mem_iUnion, Finset.mem_range, mem_Ioc] at hx
      obtain ⟨i, -, hx1, -⟩ := hx
      exact mem_Ioi.2 ((u_mem i).trans hx1)
