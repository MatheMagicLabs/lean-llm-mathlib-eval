/-
Machine-generated proof, verified by Lean.

Theorem:      GenContFract.partNum_euler_succ
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/ContinuedFractions/Euler.lean, line 173
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem partNum_euler_succ : (euler h ρ).partNums.get? (n + 1) = (ρ.get? (n + 1)).map (- ·) := by
  rw [partNums, @Stream'.Seq.map_get?, euler_s_succ]
  rcases ρ.get? (n + 1) with _ | _ <;> simp
