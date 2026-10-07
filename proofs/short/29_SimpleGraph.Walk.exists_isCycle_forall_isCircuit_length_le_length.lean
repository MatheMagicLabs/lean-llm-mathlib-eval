/-
Machine-generated proof, verified by Lean.

Theorem:      SimpleGraph.Walk.exists_isCycle_forall_isCircuit_length_le_length
Source:       Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Paths.lean, line 1060
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Combinatorics
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_isCycle_forall_isCircuit_length_le_length {v : V}
    (h : ∃ p : G.Walk v v, p.IsCircuit) :
    ∃ p : G.Walk v v, p.IsCycle ∧ ∀ p' : G.Walk v v, p'.IsCircuit → p.length ≤ p'.length := by
  classical
  obtain ⟨p, hp, hmin⟩ := exists_minimalFor_isCircuit_length h
  refine ⟨p.cycleBypass, hp.isCycle_cycleBypass, fun p' hp' ↦ ?_⟩
  refine (length_cycleBypass_le_length p).trans ?_
  rcases le_total p.length p'.length with hle | hle
  · exact hle
  · exact hmin hp' hle
