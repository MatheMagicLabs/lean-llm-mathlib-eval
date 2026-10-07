/-
Machine-generated proof, verified by Lean.

Theorem:      MvPowerSeries.optionFunLeft_mul
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPowerSeries/Equiv.lean, line 91
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  19 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma optionFunLeft_mul (p q : MvPowerSeries (Option σ) R) :
    optionFunLeft σ R (p * q) = optionFunLeft σ R p * optionFunLeft σ R q := by
  classical
  ext n x
  rw [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp_rw [coeff_mul, coeff_coeff_optionFunLeft]
  first
    | rw [← Finset.sum_product']
    | refine Eq.trans ?_ (Finset.sum_product' _ _ _)
  refine Finset.sum_nbij'
    (fun ab : (Option σ →₀ ℕ) × (Option σ →₀ ℕ) =>
      ((ab.1 none, ab.2 none), (ab.1.some, ab.2.some)))
    (fun t : (ℕ × ℕ) × ((σ →₀ ℕ) × (σ →₀ ℕ)) =>
      (t.2.1.optionElim t.1.1, t.2.2.optionElim t.1.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_antidiagonal] at h
    simp only [Finset.mem_product, Finset.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · simpa using DFunLike.congr_fun h none
    · ext v
      simpa using DFunLike.congr_fun h (Option.some v)
  · rintro ⟨⟨i, j⟩, ⟨y, z⟩⟩ h
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Finset.mem_antidiagonal]
    ext o
    cases o <;> simp
  · rintro ⟨a, b⟩ -
    refine Prod.ext ?_ ?_ <;> ext o <;> cases o <;> simp
  · rintro ⟨⟨i, j⟩, ⟨y, z⟩⟩ -
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · simp
    · simp
    · ext v
      simp
    · ext v
      simp
  · rintro ⟨a, b⟩ -
    have ha : a.some.optionElim (a none) = a := by
      ext o
      cases o <;> simp
    have hb : b.some.optionElim (b none) = b := by
      ext o
      cases o <;> simp
    simp only [ha, hb]
