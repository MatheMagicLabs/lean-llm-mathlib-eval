/-
Machine-generated proof, verified by Lean.

Theorem:      Submonoid.isMulFG_iff
Source:       Mathlib @ d0a050ad6, Mathlib/GroupTheory/Finiteness.lean, line 295
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: GroupTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem isMulFG_iff : IsMulFG P ↔ ∃ S : Finset M, Submonoid.closure (S : Set M) = P := by
  classical
  first
  | (refine Monoid.isMulFG_iff.trans ⟨?_, ?_⟩
     · rintro ⟨S, hS⟩
       refine ⟨S.image P.subtype, ?_⟩
       rw [Finset.coe_image, ← MonoidHom.map_mclosure, hS]
       first
       | rw [← MonoidHom.mrange_eq_map, range_subtype]
       | (ext x; simp)
     · rintro ⟨S, hS⟩
       first
       | (subst hS
          refine ⟨S.preimage Subtype.val Subtype.val_injective.injOn, ?_⟩
          rw [Finset.coe_preimage]
          exact closure_closure_coe_preimage)
       | (have h : (S : Set M) ⊆ Set.range P.subtype := by
            intro x hx
            refine ⟨⟨x, ?_⟩, rfl⟩
            rw [← hS]
            exact subset_closure hx
          refine ⟨S.preimage P.subtype Subtype.val_injective.injOn, ?_⟩
          apply map_injective_of_injective (f := P.subtype) Subtype.val_injective
          rw [MonoidHom.map_mclosure, Finset.coe_preimage, Set.image_preimage_eq_of_subset h,
            hS, ← MonoidHom.mrange_eq_map, range_subtype]))
  | (simp_rw [Monoid.isMulFG_iff,
       ← (map_injective_of_injective (f := P.subtype) Subtype.val_injective).eq_iff,
       ← MonoidHom.mrange_eq_map, range_subtype, MonoidHom.map_mclosure]
     refine ⟨fun ⟨S, hS⟩ ↦ ⟨S.image P.subtype, by simpa⟩,
       fun ⟨S, hS⟩ ↦ ⟨S.preimage P.subtype Subtype.val_injective.injOn, ?_⟩⟩
     have h : ↑S ⊆ Set.range (Subtype.val : P → M) := by simp [← hS]
     simpa [Set.image_preimage_eq_of_subset h])
