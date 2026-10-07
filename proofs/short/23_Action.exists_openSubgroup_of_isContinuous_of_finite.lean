/-
Machine-generated proof, verified by Lean.

Theorem:      Action.exists_openSubgroup_of_isContinuous_of_finite
Source:       Mathlib @ d0a050ad6, Mathlib/CategoryTheory/Galois/ContAction.lean, line 123
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: CategoryTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma exists_openSubgroup_of_isContinuous_of_finite
    {J : Type*} [Finite J] (obj : J → Action FintypeCat.{w} G)
    (property : ∀ j, isContinuous _ _ (obj j)) :
    ∃ (H : OpenSubgroup G), ∀ j, trivialOnSet _ H (obj j) := by
  have h : ∀ j, ∃ H : OpenSubgroup G, trivialOnSet _ H (obj j) := by
    intro j
    have hj := property j
    rw [isContinuous_eq_iSup, ObjectProperty.prop_iSup_iff] at hj
    exact hj
  choose H hH using h
  exact ⟨OpenSubgroup.iInfOfFinite H, fun j g hg ↦ hH j g (OpenSubgroup.iInfOfFinite_le H j hg)⟩
