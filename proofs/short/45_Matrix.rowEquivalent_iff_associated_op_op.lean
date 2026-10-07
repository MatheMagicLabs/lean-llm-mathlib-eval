/-
Machine-generated proof, verified by Lean.

Theorem:      Matrix.rowEquivalent_iff_associated_op_op
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/ElementaryRowOperations.lean, line 114
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  6 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma rowEquivalent_iff_associated_op_op {A B : Matrix m m R} :
    RowEquivalent A B ↔ Associated (MulOpposite.op A) (MulOpposite.op B) := by
  have hsmul : ∀ g : GL m R, g • A = (g : Matrix m m R) * A := by
    intro g
    first
      | rfl
      | simp [Units.smul_def, smul_eq_mul]
      | exact Units.smul_def g A
  have key : RowEquivalent A B ↔ ∃ g : GL m R, g • A = B := MulAction.mem_orbit_iff
  rw [key]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨Units.opEquiv.symm (MulOpposite.op g), MulOpposite.unop_injective ?_⟩
    exact (hsmul g).symm
  · rintro ⟨u, hu⟩
    refine ⟨(Units.opEquiv u).unop, ?_⟩
    rw [hsmul]
    exact congrArg MulOpposite.unop hu
