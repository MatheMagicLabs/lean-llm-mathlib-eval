/-
Machine-generated proof, verified by Lean.

Theorem:      ContinuousMap.borel_eq_iSup_comap_eval
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean, line 77
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  37 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ x : X, (borel Y).comap fun f ↦ f x := by
  refine le_antisymm ?_ iSup_comap_le_borel
  borelize Y
  have hev : ∀ (x : X) (B : Set Y), MeasurableSet B →
      @MeasurableSet C(X, Y) (⨆ x : X, (borel Y).comap fun f : C(X, Y) ↦ f x)
        {f : C(X, Y) | f x ∈ B} := by
    intro x B hB
    have hle : (borel Y).comap (fun f : C(X, Y) ↦ f x) ≤
        ⨆ x : X, (borel Y).comap fun f : C(X, Y) ↦ f x :=
      le_iSup (fun x : X ↦ (borel Y).comap fun f : C(X, Y) ↦ f x) x
    exact hle _ ⟨B, hB, rfl⟩
  have hKF : ∀ (K : Set X) (F : Set Y), IsClosed F →
      @MeasurableSet C(X, Y) (⨆ x : X, (borel Y).comap fun f : C(X, Y) ↦ f x)
        {f : C(X, Y) | Set.MapsTo f K F} := by
    intro K F hF
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (↥K)
    have heq : {f : C(X, Y) | Set.MapsTo f K F} = ⋂ z ∈ D, {f : C(X, Y) | f (z : X) ∈ F} := by
      apply Set.Subset.antisymm
      · intro f hf
        have hf' : Set.MapsTo f K F := hf
        exact Set.mem_iInter₂.2 fun z _ ↦ hf' z.2
      · intro f hf
        have hf' : ∀ z ∈ D, f (z : X) ∈ F := fun z hz ↦ Set.mem_iInter₂.1 hf z hz
        show Set.MapsTo f K F
        intro y hy
        have hmaps : Set.MapsTo (fun z : K ↦ f (z : X)) D F := by
          intro z hz
          exact hf' z hz
        have hc : Continuous (fun z : K ↦ f (z : X)) := f.continuous.comp continuous_subtype_val
        first
          | exact hF.closure_subset (map_mem_closure hc (hDd ⟨y, hy⟩) hmaps)
          | exact hF.closure_subset (hmaps.closure hc (hDd ⟨y, hy⟩))
    rw [heq]
    exact MeasurableSet.biInter hDc fun z _ ↦ hev (z : X) F hF.measurableSet
  have hKU : ∀ K : Set X, IsCompact K → ∀ U : Set Y, IsOpen U →
      @MeasurableSet C(X, Y) (⨆ x : X, (borel Y).comap fun f : C(X, Y) ↦ f x)
        {f : C(X, Y) | Set.MapsTo f K U} := by
    intro K hK U hU
    obtain ⟨T, hTc, hTo, hTU, hUT⟩ : ∃ T : Set (Set Y), T.Countable ∧ (∀ V ∈ T, IsOpen V) ∧
        (∀ V ∈ T, closure V ⊆ U) ∧ U ⊆ ⋃ V ∈ T, V := by
      refine ⟨{V | V ∈ countableBasis Y ∧ closure V ⊆ U},
        (countable_countableBasis Y).mono fun V hV ↦ hV.1,
        fun V hV ↦ (isBasis_countableBasis Y).isOpen hV.1, fun V hV ↦ hV.2, ?_⟩
      intro y hy
      obtain ⟨V, hVb, hyV, hVU⟩ : ∃ V ∈ countableBasis Y, y ∈ V ∧ closure V ⊆ U := by
        first
          | exact (isBasis_countableBasis Y).exists_closure_subset (hU.mem_nhds hy)
          | obtain ⟨W, hW, hWc, hWU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hy)
            obtain ⟨V, hVb, hyV, hVW⟩ := (isBasis_countableBasis Y).mem_nhds_iff.1 hW
            exact ⟨V, hVb, hyV, Set.Subset.trans (closure_minimal hVW hWc) hWU⟩
      exact Set.mem_biUnion (show V ∈ {V | V ∈ countableBasis Y ∧ closure V ⊆ U} from
        ⟨hVb, hVU⟩) hyV
    have heq : {f : C(X, Y) | Set.MapsTo f K U} =
        ⋃ t ∈ {t : Set (Set Y) | t.Finite ∧ t ⊆ T},
          {f : C(X, Y) | Set.MapsTo f K (⋃ V ∈ t, closure V)} := by
      apply Set.Subset.antisymm
      · intro f hf
        have hf' : Set.MapsTo f K U := hf
        obtain ⟨t, htT, htf, ht⟩ :=
          (hK.image f.continuous).elim_finite_subcover_image hTo
            (Set.Subset.trans hf'.image_subset hUT)
        refine Set.mem_biUnion (show t ∈ {t : Set (Set Y) | t.Finite ∧ t ⊆ T} from
          ⟨htf, htT⟩) ?_
        show Set.MapsTo f K (⋃ V ∈ t, closure V)
        intro y hy
        obtain ⟨V, hV, hyV⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_image_of_mem f hy))
        exact Set.mem_biUnion hV (subset_closure hyV)
      · intro f hf
        obtain ⟨t, ht, hft⟩ := Set.mem_iUnion₂.1 hf
        have hmaps : Set.MapsTo f K (⋃ V ∈ t, closure V) := hft
        show Set.MapsTo f K U
        intro y hy
        obtain ⟨V, hV, hyV⟩ := Set.mem_iUnion₂.1 (hmaps hy)
        exact hTU V (ht.2 hV) hyV
    rw [heq]
    exact MeasurableSet.biUnion (Set.countable_setOf_finite_subset hTc) fun t ht ↦
      hKF K _ (ht.1.isClosed_biUnion fun V _ ↦ isClosed_closure)
  have hb : borel C(X, Y) = MeasurableSpace.generateFrom
      (Set.image2 (fun (K : Set X) (U : Set Y) ↦ {f : C(X, Y) | Set.MapsTo f K U})
        {K | IsCompact K} {U | IsOpen U}) :=
    borel_eq_generateFrom_of_subbasis rfl
  rw [hb]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨K, hK, U, hU, rfl⟩
  exact hKU K hK U hU
