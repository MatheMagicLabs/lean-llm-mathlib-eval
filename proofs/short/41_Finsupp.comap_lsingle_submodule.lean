/-
Machine-generated proof, verified by Lean.

Theorem:      Finsupp.comap_lsingle_submodule
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Finsupp/Pi.lean, line 211
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma comap_lsingle_submodule (p : α → Submodule R M) (i : α) :
    Submodule.comap (lsingle i) (submodule p) = p i := by
  ext x
  rw [Submodule.mem_comap, mem_submodule_iff]
  constructor
  · intro hx
    simpa [lsingle_apply] using hx i
  · intro hx j
    classical
    by_cases hij : i = j
    · subst hij
      simpa [lsingle_apply] using hx
    · simp [lsingle_apply, Finsupp.single_apply, hij]
