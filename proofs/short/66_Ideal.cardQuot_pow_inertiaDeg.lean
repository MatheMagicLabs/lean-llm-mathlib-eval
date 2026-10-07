/-
Machine-generated proof, verified by Lean.

Theorem:      Ideal.cardQuot_pow_inertiaDeg
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/RamificationInertia/Inertia.lean, line 177
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem cardQuot_pow_inertiaDeg [Module.Finite R S] [p.IsMaximal] [q.IsMaximal] [q.LiesOver p] :
    p.cardQuot ^ q.inertiaDeg R = q.cardQuot := by
  have hfin : Module.Finite (R ⧸ p) (S ⧸ q) := by
    first
      | infer_instance
      | exact module_finite_of_liesOver q p
      | exact module_finite_of_liesOver p q
      | exact Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ q)
      | (haveI : Module.Finite R (S ⧸ q) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ R q).toLinearMap (Ideal.Quotient.mkₐ_surjective R q); exact Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ q))
  have key : Nat.card (S ⧸ q) = Nat.card (R ⧸ p) ^ Module.finrank (R ⧸ p) (S ⧸ q) := by
    letI : Field (R ⧸ p) := Quotient.field p
    haveI : Module.Finite (R ⧸ p) (S ⧸ q) := hfin
    first
      | exact Module.natCard_eq_pow_finrank
      | exact Module.natCard_eq_pow_finrank (R ⧸ p) (S ⧸ q)
      | (rw [Nat.card_congr (Module.finBasis (R ⧸ p) (S ⧸ q)).equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]; done)
      | (rw [Nat.card_congr (Module.finBasis (R ⧸ p) (S ⧸ q)).equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]; rfl)
  have hp : p.cardQuot = Nat.card (R ⧸ p) := by
    first
      | rfl
      | exact Submodule.cardQuot_apply p
      | simp [Submodule.cardQuot_apply]
  have hq : q.cardQuot = Nat.card (S ⧸ q) := by
    first
      | rfl
      | exact Submodule.cardQuot_apply q
      | simp [Submodule.cardQuot_apply]
  rw [inertiaDeg_eq_of_isMaximal p q, hp, hq]
  exact key.symm
