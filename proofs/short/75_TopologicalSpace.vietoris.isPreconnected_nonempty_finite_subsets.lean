/-
Machine-generated proof, verified by Lean.

Theorem:      TopologicalSpace.vietoris.isPreconnected_nonempty_finite_subsets
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/Sets/VietorisTopology.lean, line 333
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  13 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem isPreconnected_nonempty_finite_subsets {s : Set α} (hs : IsPreconnected s) :
    IsPreconnected {t | t.Nonempty ∧ t.Finite ∧ t ⊆ s} := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · have hemp : {t : Set α | t.Nonempty ∧ t.Finite ∧ t ⊆ ∅} = ∅ := by
      ext t
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨y, hy⟩, -, hts⟩
      exact hts hy
    rw [hemp]
    exact isPreconnected_empty
  · have key : {t : Set α | t.Nonempty ∧ t.Finite ∧ t ⊆ s} =
        ⋃ n : ℕ, (range : (Fin (n + 1) → α) → Set α) '' (univ.pi fun _ => s) := by
      ext t
      simp only [mem_setOf_eq, mem_iUnion, mem_image, mem_univ_pi]
      constructor
      · rintro ⟨hne, hfin, hts⟩
        obtain ⟨n, f, hf⟩ := hfin.fin_embedding
        cases n with
        | zero =>
          exfalso
          rw [← hf] at hne
          obtain ⟨y, i, -⟩ := hne
          exact i.elim0
        | succ n =>
          refine ⟨n, f, fun i => hts ?_, hf⟩
          rw [← hf]
          exact mem_range_self i
      · rintro ⟨n, f, hf, rfl⟩
        exact ⟨range_nonempty f, finite_range f, range_subset_iff.mpr hf⟩
    rw [key]
    refine isPreconnected_iUnion
      ⟨{x}, mem_iInter.mpr fun n => ⟨fun _ => x, fun _ _ => hx, range_const⟩⟩ fun n => ?_
    exact (isPreconnected_univ_pi fun _ => hs).image _ continuous_range_of_finite.continuousOn
