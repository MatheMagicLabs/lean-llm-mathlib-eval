/-
Machine-generated proof, verified by Lean.

Theorem:      Rat.num_or_den_zero_padicVal
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/Padics/PadicVal/Basic.lean, line 380
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem num_or_den_zero_padicVal (a : ℚ) {p : ℕ} (hp : p.Prime) :
    padicValInt p a.num = 0 ∨ padicValNat p a.den = 0 := by
  by_cases h : p ∣ a.num.natAbs
  · right
    apply padicValNat.eq_zero_of_not_dvd
    first
      | exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left h a.reduced)
      | exact fun hd => (Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, h, hd⟩) a.reduced
  · left
    apply padicValInt.eq_zero_of_not_dvd
    first
      | rwa [Int.ofNat_dvd_left]
      | exact fun hd => h (Int.natCast_dvd.mp hd)
      | exact fun hd => h (Int.ofNat_dvd_left.mp hd)
