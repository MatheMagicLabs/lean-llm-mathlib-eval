/-
Machine-generated proof, verified by Lean.

Theorem:      IsNowhereDense.biUnion
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/GDelta/Basic.lean, line 221
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

protected lemma IsNowhereDense.biUnion {u : Finset ι} {f : ι → Set X}
    (hf : ∀ i ∈ u, IsNowhereDense (f i)) : IsNowhereDense (⋃ i ∈ u, f i) := by
  classical
  revert hf
  refine Finset.induction_on u ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.set_biUnion_insert]
    exact (hf a (Finset.mem_insert_self a s)).union
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
