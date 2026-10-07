/-
Machine-generated proof, verified by Lean.

Theorem:      Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/Ideal/Operations.lean, line 1233
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma subset_iUnion_iff_mem_of_isMaximal_of_finite
    {R : Type*} [CommRing R] {M : Ideal R} [M.IsMaximal] {S : Set (Ideal R)}
    (hs : S.Finite) (a b : Ideal R) (hp : ∀ I ∈ S, I ≠ a → I ≠ b → I.IsPrime)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) : ((M : Set R) ⊆ ⋃ I ∈ S, I) ↔ M ∈ S := by
  refine (Ideal.subset_union_prime_finite hs a b hp).trans ⟨?_, fun hM => ⟨M, hM, le_rfl⟩⟩
  rintro ⟨I, hI, hMI⟩
  have hIt : I ≠ ⊤ := by
    by_cases hIa : I = a
    · rw [hIa]
      exact ha
    by_cases hIb : I = b
    · rw [hIb]
      exact hb
    exact (hp I hI hIa hIb).ne_top
  have hMI' : M = I := Ideal.IsMaximal.eq_of_le ‹M.IsMaximal› hIt hMI
  rw [hMI']
  exact hI
