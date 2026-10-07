/-
Machine-generated proof, verified by Lean.

Theorem:      Sym2.diag_diagElem
Source:       Mathlib @ d0a050ad6, Mathlib/Data/Sym/Sym2.lean, line 538
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Data
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem diag_diagElem (h : z.IsDiag) : diag (z.diagElem h) = z := by
  obtain ⟨a, b⟩ := z
  have hab : a = b := h
  subst hab
  rfl
