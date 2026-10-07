/-
Machine-generated proof, verified by Lean.

Theorem:      Matrix.IsTotallyNonneg.nonneg
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Determinant/TotallyNonneg.lean, line 50
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma IsTotallyNonneg.nonneg (hM : M.IsTotallyNonneg) (i j : ι) : 0 ≤ M i j := by
  have h : 0 ≤ (M.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)).det :=
    hM (fun a b hab => (hab.ne (Subsingleton.elim a b)).elim)
      (fun a b hab => (hab.ne (Subsingleton.elim a b)).elim)
  simpa [Matrix.det_fin_one] using h
