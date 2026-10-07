/-
Machine-generated proof, verified by Lean.

Theorem:      Nat.dvd_prod_primeFactors_pow_self
Source:       Mathlib @ d0a050ad6, Mathlib/Data/Nat/Factorization/Basic.lean, line 506
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Data
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem dvd_prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    n ∣ (∏ p ∈ n.primeFactors, p) ^ n := by
  calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := prod_primeFactors_pow_factorization hn
    _ ∣ ∏ p ∈ n.primeFactors, p ^ n := by
        apply Finset.prod_dvd_prod_of_dvd
        intro p _
        exact pow_dvd_pow p (factorization_lt p hn).le
    _ = (∏ p ∈ n.primeFactors, p) ^ n := by rw [Finset.prod_pow]
