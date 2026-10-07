/-
Machine-generated proof, verified by Lean.

Theorem:      QuadraticAlgebra.changeGenerator_relation
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/QuadraticAlgebra/Basic.lean, line 437
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private theorem changeGenerator_relation (a b u k : R) :
    (u • ω + algebraMap R (QuadraticAlgebra R a b) k) *
        (u • ω + algebraMap R (QuadraticAlgebra R a b) k) =
      (u ^ 2 * a - u * b * k - k ^ 2) • 1 +
        (u * b + 2 * k) • (u • ω + algebraMap R (QuadraticAlgebra R a b) k) := by
  ext <;> simp <;> ring
