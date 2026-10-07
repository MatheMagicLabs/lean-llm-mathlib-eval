/-
Machine-generated proof, verified by Lean.

Theorem:      IsPGroup.dvd_orderOf
Source:       Mathlib @ d0a050ad6, Mathlib/GroupTheory/PGroup.lean, line 80
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: GroupTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem dvd_orderOf [Fact p.Prime] (hG : IsPGroup p G) {g : G} (hg : g ≠ 1) : p ∣ orderOf g := by
  obtain ⟨k, hk⟩ := hG.exists_orderOf_eq_pow g
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact absurd hk hg
  · rw [hk]
    first
    | exact dvd_pow_self p (Nat.succ_ne_zero k)
    | exact dvd_pow_self p (by omega)
    | rw [pow_succ]
      exact dvd_mul_left p _
