/-
Machine-generated proof, verified by Lean.

Theorem:      Polynomial.associated_content_mul
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/Polynomial/Content.lean, line 321
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  32 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem associated_content_mul (p q : R[X]) :
    Associated ((p * q).content) (p.content * q.content) := by
  suffices H : ∀ n : ℕ, ∀ p q : R[X], p.natDegree + q.natDegree < n →
      Associated ((p * q).content) (p.content * q.content) by
    exact H _ p q (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero =>
    intro p q h
    exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro p q hpq
    have key : ∀ P Q : R[X], P.content = 1 → Q.content = 1 →
        P.natDegree + Q.natDegree < n + 1 → IsUnit (P * Q).content := by
      intro P Q hP hQ hPQ
      have hA : IsUnit (gcd (P * Q).eraseLead.content P.leadingCoeff) := by
        have h1 : Associated (P.eraseLead * Q).content P.eraseLead.content := by
          by_cases h0 : P.eraseLead = 0
          · exact Associated.of_eq (by rw [h0, zero_mul])
          have h : P.eraseLead.natDegree < P.natDegree := by
            first
            | exact (eraseLead_natDegree_lt_or_eraseLead_eq_zero P).resolve_right h0
            | exact natDegree_lt_natDegree h0 (degree_eraseLead_lt fun hP0 => h0 (by rw [hP0, eraseLead_zero]))
          have := ih P.eraseLead Q (by omega)
          rwa [hQ, mul_one] at this
        have h2 : gcd P.eraseLead.content P.leadingCoeff = 1 := by
          rw [gcd_comm, ← content_eq_gcd_leadingCoeff_content_eraseLead, hP]
        rw [content_mul_aux]
        exact isUnit_of_dvd_one ((dvd_gcd ((gcd_dvd_left _ _).trans h1.dvd)
          (gcd_dvd_right _ _)).trans (dvd_of_eq h2))
      have hB : IsUnit (gcd (P * Q).eraseLead.content Q.leadingCoeff) := by
        have h1 : Associated (Q.eraseLead * P).content Q.eraseLead.content := by
          by_cases h0 : Q.eraseLead = 0
          · exact Associated.of_eq (by rw [h0, zero_mul])
          have h : Q.eraseLead.natDegree < Q.natDegree := by
            first
            | exact (eraseLead_natDegree_lt_or_eraseLead_eq_zero Q).resolve_right h0
            | exact natDegree_lt_natDegree h0 (degree_eraseLead_lt fun hQ0 => h0 (by rw [hQ0, eraseLead_zero]))
          have := ih Q.eraseLead P (by omega)
          rwa [hP, mul_one] at this
        have h2 : gcd Q.eraseLead.content Q.leadingCoeff = 1 := by
          rw [gcd_comm, ← content_eq_gcd_leadingCoeff_content_eraseLead, hQ]
        rw [mul_comm P Q, content_mul_aux]
        exact isUnit_of_dvd_one ((dvd_gcd ((gcd_dvd_left _ _).trans h1.dvd)
          (gcd_dvd_right _ _)).trans (dvd_of_eq h2))
      rw [content_eq_gcd_leadingCoeff_content_eraseLead, leadingCoeff_mul, gcd_comm]
      exact isUnit_of_dvd_one ((gcd_mul_dvd_mul_gcd _ _ _).trans
        (isUnit_iff_dvd_one.mp (hA.mul hB)))
    have key' : IsUnit (p.primPart * q.primPart).content :=
      key _ _ p.content_primPart q.content_primPart
        (by rw [p.natDegree_primPart, q.natDegree_primPart]; exact hpq)
    have e1 : p * q = C (p.content * q.content) * (p.primPart * q.primPart) := by
      conv_lhs => rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
      rw [C_mul]
      ring
    rw [e1]
    refine (associated_content_C_mul _ _).trans ?_
    first
    | exact associated_mul_unit_left _ _ key'
    | simpa using (associated_one_iff_isUnit.mpr key').mul_left (p.content * q.content)
