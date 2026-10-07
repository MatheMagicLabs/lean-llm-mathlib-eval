/-
Machine-generated proof, verified by Lean.

Theorem:      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/RamificationInertia/Ramification.lean, line 366
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem emultiplicity_map_eq_ramificationIdx'_mul [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {I : Ideal R} (h : I ≠ ⊥)
    (hv : Irreducible v) (hw : Irreducible w) (hw_bot : w ≠ ⊥) [w.LiesOver v] :
    emultiplicity w (I.map (algebraMap R S)) =
      v.ramificationIdx' w * emultiplicity v I := by
  have hwp : Prime w := hw.prime
  have hvp : Prime v := hv.prime
  revert h
  first
    | refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
    | refine WfDvdMonoid.induction_on_irreducible I ?_ ?_ ?_
  · intro h0
    exact absurd Ideal.zero_eq_bot h0
  · intro x hx _
    have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
    have hux : IsUnit (Ideal.map (algebraMap R S) x) := by
      rw [hx', Ideal.map_top]
      exact Ideal.isUnit_iff.mpr rfl
    have e1 : emultiplicity w (Ideal.map (algebraMap R S) x) = 0 :=
      emultiplicity_eq_zero.mpr fun hd => hw.not_isUnit (isUnit_of_dvd_unit hd hux)
    have e2 : emultiplicity v x = 0 :=
      emultiplicity_eq_zero.mpr fun hd => hv.not_isUnit (isUnit_of_dvd_unit hd hx)
    rw [e1, e2, mul_zero]
  · intro a p ha hp ih _
    have hp' : Prime p := by
      first
        | exact hp
        | exact hp.prime
    have ha' : a ≠ ⊥ := fun h0 => ha (h0.trans Ideal.zero_eq_bot.symm)
    rw [Ideal.map_mul, emultiplicity_mul hwp, emultiplicity_mul hvp, ih ha',
      emultiplicity_map_eq_ramificationIdx'_mul_of_prime hv hp' hw hw_bot, mul_add]
