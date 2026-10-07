/-
Machine-generated proof, verified by Lean.

Theorem:      Chebyshev.sum_PrimePow_eq_sum_sum'
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/Chebyshev.lean, line 336
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  30 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem sum_PrimePow_eq_sum_sum' {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x)
  {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ Icc 1 N, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_nbij (fun a : (Σ _ : ℕ, ℕ) ↦ a.2 ^ a.1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · rintro ⟨k, p⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc] at h ⊢
    obtain ⟨⟨hk1, -⟩, ⟨hp0, hpx⟩, hp⟩ := h
    have hk0 : k ≠ 0 := by omega
    refine ⟨⟨pow_pos hp0 k, ?_⟩, ?_⟩
    · apply Nat.le_floor
      have h1 : (p : ℝ) ≤ x ^ ((1 : ℝ) / k) := by
        have h2 := Nat.floor_le (Real.rpow_nonneg hx ((1 : ℝ) / k))
        exact le_trans (by exact_mod_cast hpx) h2
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
      calc ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by norm_cast
        _ ≤ (x ^ ((1 : ℝ) / k)) ^ k := by
          first
            | exact pow_le_pow_left₀ (Nat.cast_nonneg p) h1 k
            | exact pow_le_pow_left (Nat.cast_nonneg p) h1 k
            | gcongr
        _ = x := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel hkR, Real.rpow_one]
    · first
        | exact hp.isPrimePow.pow hk0
        | (rw [isPrimePow_nat_iff]; exact ⟨p, k, hp, Nat.pos_of_ne_zero hk0, rfl⟩)
  · rintro ⟨k, p⟩ h ⟨l, q⟩ h' heq
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_Ioc] at h h'
    obtain ⟨⟨hk1, -⟩, -, hp⟩ := h
    obtain ⟨⟨hl1, -⟩, -, hq⟩ := h'
    have heq' : p ^ k = q ^ l := heq
    have hpq : p = q := by
      have h1 : p ∣ q ^ l := by
        rw [← heq']
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
    subst hpq
    have hkl : k = l := Nat.pow_right_injective hp.two_le heq'
    subst hkl
    rfl
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨-, hnx⟩, hpp⟩ := hn
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    refine ⟨⟨k, p⟩, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_Ioc]
    have hk0 : k ≠ 0 := by omega
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    have hpk : (p : ℝ) ^ k ≤ x := by
      have h1 : ((p ^ k : ℕ) : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) (Nat.floor_le hx)
      exact_mod_cast h1
    have h2k : (2 : ℝ) ^ k ≤ x := by
      calc (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := by
            gcongr
            exact_mod_cast hp.two_le
        _ ≤ x := hpk
    have hkN : k ≤ N := by
      refine le_trans ?_ hN
      apply Nat.le_floor
      rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
      exact Real.log_le_log (by positivity) h2k
    have hpx : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
      apply Nat.le_floor
      calc (p : ℝ) = ((p : ℝ) ^ k) ^ ((1 : ℝ) / k) := by
            first
              | rw [one_div, Real.pow_rpow_inv_natCast (Nat.cast_nonneg p) hk0]
              | rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
                  mul_one_div_cancel hkR, Real.rpow_one]
        _ ≤ x ^ ((1 : ℝ) / k) :=
            Real.rpow_le_rpow (by positivity) hpk (by positivity)
    exact ⟨⟨by omega, hkN⟩, ⟨hp.pos, hpx⟩, hp⟩
