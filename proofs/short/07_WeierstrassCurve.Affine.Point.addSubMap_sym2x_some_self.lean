/-
Machine-generated proof, verified by Lean.

Theorem:      WeierstrassCurve.Affine.Point.addSubMap_sym2x_some_self
Source:       Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean, line 214
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: AlgebraicGeometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (6.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma addSubMap_sym2x_some_self {x y : F} (h : W.Nonsingular x y) :
    (addSubMap W · |>.eval <| sym2x (some x y h) (some x y h)) =
      ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
  ext i : 1
  fin_cases i <;> simp [addSubMap] <;> ring
