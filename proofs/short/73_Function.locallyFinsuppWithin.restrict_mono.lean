/-
Machine-generated proof, verified by Lean.

Theorem:      Function.locallyFinsuppWithin.restrict_mono
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/LocallyFinsupp.lean, line 642
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma restrict_mono [Zero Y] [LinearOrder Y] {A B : locallyFinsuppWithin U Y} {V : Set X}
    (hVU : V ⊆ U) (hAB : A ≤ B) :
    A.restrict hVU ≤ B.restrict hVU := by
  intro x
  by_cases hx : x ∈ V
  · simp [restrict_apply, hx, hAB x]
  · simp [restrict_apply, hx]
