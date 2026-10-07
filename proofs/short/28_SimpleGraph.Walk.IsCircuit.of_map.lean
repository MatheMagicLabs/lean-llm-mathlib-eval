/-
Machine-generated proof, verified by Lean.

Theorem:      SimpleGraph.Walk.IsCircuit.of_map
Source:       Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Paths.lean, line 1107
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Combinatorics
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

protected theorem IsCircuit.of_map {p : G.Walk u u} (hp : (p.map f).IsCircuit) : p.IsCircuit := by
  refine ⟨IsTrail.of_map hp.isTrail, fun h ↦ hp.ne_nil ?_⟩
  subst h
  first
  | rfl
  | simp
