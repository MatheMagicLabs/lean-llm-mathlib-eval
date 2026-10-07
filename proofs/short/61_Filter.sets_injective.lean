/-
Machine-generated proof, verified by Lean.

Theorem:      Filter.sets_injective
Source:       Mathlib @ d0a050ad6, Mathlib/Order/Filter/Basic.lean, line 113
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Order
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem sets_injective : Injective (Filter.sets : Filter α → Set (Set α)) := by
  intro f g h
  first
  | exact filter_eq h
  | exact Filter.filter_eq h
  | (cases f; cases g; congr)
