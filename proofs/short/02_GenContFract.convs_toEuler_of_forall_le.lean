/-
Machine-generated proof, verified by Lean.

Theorem:      GenContFract.convs_toEuler_of_forall_le
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/ContinuedFractions/Euler.lean, line 267
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  17 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem convs_toEuler_of_forall_le (hB : ∀ m ≤ n, g.dens m ≠ 0) :
    ∀ m ≤ n, g.toEuler.convs m = g.convs m := by
  have alg1 : ∀ (a b x : K), b ≠ 0 → (1 * x + a / b) * b = b * x + a := by
    intro a b x hb
    calc (1 * x + a / b) * b = x * b + a * (b * b⁻¹) := by ring
      _ = b * x + a := by rw [mul_inv_cancel₀ hb, mul_one]; ring
  have alg2 : ∀ (a b E0 E1 E2 A0 A1 A2 B0 B1 B2 : K), B2 ≠ 0 →
      E2 = (1 - a * B0 / B2) * E1 + a * B0 / B2 * E0 →
      A2 = b * A1 + a * A0 → B2 = b * B1 + a * B0 →
      E0 * B0 = A0 → E1 * B1 = A1 → E2 * B2 = A2 := by
    intro a b E0 E1 E2 A0 A1 A2 B0 B1 B2 hB2 hE hA hBr h0 h1
    subst hE hA h0 h1
    calc ((1 - a * B0 / B2) * E1 + a * B0 / B2 * E0) * B2
        = E1 * B2 + (a * B0 * E0 - a * B0 * E1) * (B2 * B2⁻¹) := by ring
      _ = E1 * B2 + (a * B0 * E0 - a * B0 * E1) := by rw [mul_inv_cancel₀ hB2, mul_one]
      _ = E1 * (b * B1 + a * B0) + (a * B0 * E0 - a * B0 * E1) := by rw [← hBr]
      _ = b * (E1 * B1) + a * (E0 * B0) := by ring
  have key : ∀ m, m ≤ n → g.toEuler.nums m * g.dens m = g.nums m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 =>
        intro _
        show g.toEuler.nums 0 * g.dens 0 = g.nums 0
        simp only [zeroth_num_eq_h, zeroth_den_eq_one, mul_one, toEuler_h]
      | 1 =>
        intro hm1
        show g.toEuler.nums 1 * g.dens 1 = g.nums 1
        rcases hs : g.s.get? 0 with _ | ⟨a, b⟩
        · have hT : g.TerminatedAt 0 := hs
          have hT' : g.toEuler.TerminatedAt 0 := terminatedAt_toEuler.mpr hT
          rw [nums_stable_of_terminated (Nat.zero_le 1) hT',
            dens_stable_of_terminated (Nat.zero_le 1) hT,
            nums_stable_of_terminated (Nat.zero_le 1) hT]
          simp only [zeroth_num_eq_h, zeroth_den_eq_one, mul_one, toEuler_h]
        · have hs' : g.toEuler.s.get? 0 = some ⟨a / b, 1⟩ := by
            rw [toEuler_s_zero, hs]
            try rfl
          have hB1 : g.dens 1 = b := first_den_eq hs
          have hA1 : g.nums 1 = b * g.h + a := first_num_eq hs
          have hE1 : g.toEuler.nums 1 = 1 * g.h + a / b := first_num_eq hs'
          have hb : b ≠ 0 := by
            rw [← hB1]
            exact hB 1 hm1
          rw [hE1, hB1, hA1]
          exact alg1 a b g.h hb
      | k + 2 =>
        intro hm2
        show g.toEuler.nums (k + 2) * g.dens (k + 2) = g.nums (k + 2)
        have ih0 := ih k (by omega) (by omega)
        have ih1 := ih (k + 1) (by omega) (by omega)
        rcases hs : g.s.get? (k + 1) with _ | ⟨a, b⟩
        · have hT : g.TerminatedAt (k + 1) := hs
          have hT' : g.toEuler.TerminatedAt (k + 1) := terminatedAt_toEuler.mpr hT
          rw [nums_stable_of_terminated (show k + 1 ≤ k + 2 by omega) hT',
            dens_stable_of_terminated (show k + 1 ≤ k + 2 by omega) hT,
            nums_stable_of_terminated (show k + 1 ≤ k + 2 by omega) hT]
          exact ih1
        · have hs' : g.toEuler.s.get? (k + 1) =
              some ⟨a * g.dens k / g.dens (k + 2), 1 - a * g.dens k / g.dens (k + 2)⟩ := by
            rw [toEuler_s_succ, hs]
            try rfl
          have hA : g.nums (k + 2) = b * g.nums (k + 1) + a * g.nums k :=
            nums_recurrence hs rfl rfl
          have hBr : g.dens (k + 2) = b * g.dens (k + 1) + a * g.dens k :=
            dens_recurrence hs rfl rfl
          have hE : g.toEuler.nums (k + 2) =
              (1 - a * g.dens k / g.dens (k + 2)) * g.toEuler.nums (k + 1) +
                a * g.dens k / g.dens (k + 2) * g.toEuler.nums k :=
            nums_recurrence hs' rfl rfl
          exact alg2 _ _ _ _ _ _ _ _ _ _ _ (hB (k + 2) hm2) hE hA hBr ih0 ih1
  intro m hm
  have hE0 : g.toEuler.convs m = g.toEuler.nums m / g.toEuler.dens m := rfl
  have hC : g.convs m = g.nums m / g.dens m := rfl
  rw [hE0, hC, IsEuler.dens_eq_one isEuler_toEuler, div_one, eq_div_iff (hB m hm)]
  exact key m hm
