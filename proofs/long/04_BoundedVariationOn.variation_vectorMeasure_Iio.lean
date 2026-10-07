/-
Machine-generated proof, verified by Lean.

Theorem:      BoundedVariationOn.variation_vectorMeasure_Iio
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean, line 484
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  28 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma variation_vectorMeasure_Iio (hf : BoundedVariationOn f univ) {a : α} :
    hf.vectorMeasure.variation (Iio a) = eVariationOn f.leftLim (Iio a) := by
  by_cases hb : ∃ b : α, IsBot b
  · rcases hb with ⟨b, hb⟩
    have hI : Iio a = Ico b a := by
      ext x
      simp only [mem_Iio, mem_Ico]
      exact ⟨fun h ↦ ⟨hb x, h⟩, fun h ↦ h.2⟩
    rw [hI, variation_vectorMeasure_Ico hf]
  apply le_antisymm
  · have : Nonempty α := ⟨a⟩
    obtain ⟨u, u_anti, hu⟩ : ∃ u : ℕ → α, Antitone u ∧ Tendsto u atTop atBot :=
      Filter.exists_seq_antitone_tendsto_atTop_atBot α
    have A : Tendsto (fun n ↦ hf.vectorMeasure.variation (Ico (u n) a)) atTop
        (𝓝 (hf.vectorMeasure.variation (Iio a))) := by
      have hU : Iio a = ⋃ n, Ico (u n) a := by
        refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun n ↦ Set.Ico_subset_Iio_self)
        intro x hx
        obtain ⟨n, hn⟩ := (hu.eventually (Iic_mem_atBot x)).exists
        exact mem_iUnion.2 ⟨n, ⟨hn, hx⟩⟩
      rw [hU]
      exact tendsto_measure_iUnion_atTop
        (by intro i j hij; exact Set.Ico_subset_Ico_left (u_anti hij))
    apply le_of_tendsto A
    filter_upwards with n
    rw [variation_vectorMeasure_Ico hf]
    apply eVariationOn.mono
    exact Set.Ico_subset_Iio_self
  · simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall, mem_Iio, and_imp]
    intro n u u_mono hu
    obtain ⟨b, hb'⟩ : ∃ b, b < u 0 := by
      simp only [IsBot, not_exists, not_forall, not_le] at hb
      exact hb (u 0)
    have us : ∀ i, u i ∈ Ioo b a := fun i ↦ ⟨hb'.trans_le (u_mono (Nat.zero_le i)), hu i⟩
    first
      | apply (eVariationOn.sum_le_of_monotoneOn_Iic (s := Ioo b a) (u_mono.monotoneOn _)
          (fun i _ ↦ us i)).trans
      | apply (eVariationOn.sum_le_of_monotoneOn_Iic _ (s := Ioo b a) (u_mono.monotoneOn _)
          (fun i _ ↦ us i)).trans
      | apply (eVariationOn.sum_le _ n u_mono us).trans
      | apply (eVariationOn.sum_le n u_mono us).trans
    rw [← variation_vectorMeasure_Ioo_left hf]
    exact measure_mono Set.Ioo_subset_Iio_self
