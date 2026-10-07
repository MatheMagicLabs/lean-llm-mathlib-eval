/-
Machine-generated proof, verified by Lean.

Theorem:      SimpleGraph.IsBridge.anti
Source:       Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean, line 885
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Combinatorics
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem IsBridge.anti {G' : SimpleGraph V} {e : Sym2 V} (hG : G ≤ G') (h : G'.IsBridge e) :
    G.IsBridge e := by
  cases e with
  | h u v =>
    have hle : G.deleteEdges {s(u, v)} ≤ G'.deleteEdges {s(u, v)} := by
      intro a b hab
      rw [deleteEdges_adj] at hab ⊢
      exact ⟨hG hab.1, hab.2⟩
    exact isBridge_iff.mpr fun hr => isBridge_iff.mp h (hr.mono hle)
