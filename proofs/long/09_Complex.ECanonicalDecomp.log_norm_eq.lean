/-
Machine-generated proof, verified by Lean.

Theorem:      Complex.ECanonicalDecomp.log_norm_eq
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/CanonicalDecomposition.lean, line 621
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  27 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma ECanonicalDecomp.log_norm_eq
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    Real.log ‖h w‖ = ((∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖)
          - (∑ᶠ i, (divisor f (sphere 0 R) i) * Real.log ‖w - i‖))
          + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
  have hb : (divisor f (ball (0 : ℂ) R)).support.Finite :=
    D.meromorphicOn.divisor_ball_support_finite
  have hs : (divisor f (sphere (0 : ℂ) R)).support.Finite :=
    (divisor f (sphere (0 : ℂ) R)).finiteSupport (isCompact_sphere 0 R)
  have key : ∀ (g : ℂ → ℂ) (d : ℂ → ℤ), d.support.Finite → (∀ i, d i ≠ 0 → g i ≠ 0) →
      Real.log ‖∏ᶠ i, g i ^ d i‖ = ∑ᶠ i, (d i : ℝ) * Real.log ‖g i‖ := by
    intro g d hd hg
    have h₁ : (Function.mulSupport fun i ↦ g i ^ d i) ⊆ (hd.toFinset : Set ℂ) := by
      intro i hi
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      rw [Function.mem_mulSupport] at hi
      contrapose! hi
      simp [hi]
    have h₂ : (Function.support fun i ↦ (d i : ℝ) * Real.log ‖g i‖) ⊆
        (hd.toFinset : Set ℂ) := by
      intro i hi
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      rw [Function.mem_support] at hi
      contrapose! hi
      simp [hi]
    rw [finprod_eq_prod_of_mulSupport_subset _ h₁, finsum_eq_sum_of_support_subset _ h₂,
      norm_prod, Real.log_prod]
    · simp only [norm_zpow, Real.log_zpow]
    · intro i hi
      rw [Set.Finite.mem_toFinset] at hi
      exact norm_ne_zero_iff.mpr (zpow_ne_zero _ (hg i (Function.mem_support.mp hi)))
  have hA' : Real.log ‖∏ᶠ i, canonicalFactor R i w ^ (divisor f (ball 0 R)) i‖ =
      ∑ᶠ i, ((divisor f (ball 0 R)) i : ℝ) * Real.log ‖canonicalFactor R i w‖ := by
    refine key (fun i ↦ canonicalFactor R i w) (divisor f (ball 0 R)) hb fun i hi ↦ ?_
    have h₁i : i ∈ ball (0 : ℂ) R := (divisor f (ball 0 R)).supportWithinDomain hi
    have h₂i : w ≠ i := by
      rintro rfl
      exact hi (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁i, h₂w])
    exact canonicalFactor_ne_zero h₁i h₁w h₂i
  have hB' : Real.log ‖∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i‖ =
      -∑ᶠ i, ((divisor f (sphere 0 R)) i : ℝ) * Real.log ‖w - i‖ := by
    simp only [locallyFinsuppWithin.coe_neg, Pi.neg_apply, zpow_neg, finprod_inv_distrib,
      norm_inv, Real.log_inv, neg_inj]
    refine key (fun i ↦ w - i) (divisor f (sphere 0 R)) hs fun i hi ↦ ?_
    have h₁i : i ∈ sphere (0 : ℂ) R := (divisor f (sphere 0 R)).supportWithinDomain hi
    show w - i ≠ 0
    rw [sub_ne_zero]
    rintro rfl
    exact hi (by simp [(D.meromorphicOn.mono_set sphere_subset_closedBall).divisor_apply h₁i, h₂w])
  have hne : ‖h w‖ ≠ 0 := norm_ne_zero_iff.mpr (D.ne_zero w h₁w)
  rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt h₁w h₂w hR,
    norm_smul, norm_mul] at hne ⊢
  obtain ⟨hAB, hc⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp hAB
  rw [Real.log_mul hAB hc, Real.log_mul hA hB]
  linarith [hA', hB']
