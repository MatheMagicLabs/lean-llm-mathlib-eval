/-
Machine-generated proof, verified by Lean.

Theorem:      CategoryTheory.Precoverage.toGrothendieck_comap_eq_restrictedTopology
Source:       Mathlib @ d0a050ad6, Mathlib/CategoryTheory/Sites/DenseSubsite/InducedTopology.lean, line 186
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  10 tactic steps; area: CategoryTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma toGrothendieck_comap_eq_restrictedTopology [F.Faithful] [F.Full]
    (H : ∀ {S : C} {R : Presieve (F.obj S)}, R ∈ K (F.obj S) →
      Presieve.map F (Presieve.functorPullback F R) ∈ K (F.obj S)) :
    (K.comap F).toGrothendieck = F.restrictedTopology K.toGrothendieck := by
  have := locallyCoverDense_of_map_functorPullback_mem F K H
  apply le_antisymm
  · first
      | rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
      | rw [Precoverage.toGrothendieck_le_iff]
    intro X R hR
    have hR' : Presieve.map F R ∈ K (F.obj X) := hR
    first
      | rw [GrothendieckTopology.mem_toPrecoverage_iff]
      | change Sieve.generate R ∈ F.restrictedTopology K.toGrothendieck X
    rw [Functor.mem_restrictedTopology_iff,
      Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
    refine ⟨Presieve.map F R, hR', ?_⟩
    rintro _ _ ⟨hf⟩
    first
      | exact ⟨_, _, 𝟙 _, Sieve.le_generate R _ hf, (Category.id_comp _).symm⟩
      | exact ⟨_, _, 𝟙 _, ⟨_, 𝟙 _, _, hf, Category.id_comp _⟩, (Category.id_comp _).symm⟩
  · intro X S hS
    rw [Functor.mem_restrictedTopology_iff,
      Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
    obtain ⟨R, hR, hle⟩ := hS
    have hgen : Sieve.generate (Presieve.functorPullback F R) ∈ (K.comap F).toGrothendieck X := by
      first
        | exact Precoverage.generate_mem_toGrothendieck (H hR)
        | exact (K.comap F).generate_mem_toGrothendieck (H hR)
        | exact (Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mp le_rfl) X (H hR)
    refine (K.comap F).toGrothendieck.superset_covering ?_ hgen
    rw [Sieve.generate_le_iff]
    intro Y g hg
    have hFg : (Sieve.functorPushforward F S).arrows (F.map g) := by
      first
        | exact hle _ (F.map g) hg
        | exact hle _ _ hg
        | exact hle hg
        | exact hle _ hg
    obtain ⟨Z, g', h, hg', e⟩ := hFg
    obtain ⟨h', rfl⟩ := F.map_surjective h
    have hgg : g = h' ≫ g' := F.map_injective (e.trans (F.map_comp h' g').symm)
    subst hgg
    exact S.downward_closed hg' h'
