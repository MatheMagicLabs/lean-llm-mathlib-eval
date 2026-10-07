/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_not_aestronglyMeasurable_ennreal
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 199
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  30 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_not_aestronglyMeasurable_ennreal
    (p q r : ℝ≥0∞) (b : E → F → G) (c : ℝ≥0∞)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    (hfg : ¬ (AEStronglyMeasurable f μ ∧ AEStronglyMeasurable g μ))
    (hp : p ≠ 0) (hq : q ≠ 0) :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ := by
  have H1 : eLpNorm f p μ = ∞ ∨ eLpNorm g q μ = ∞ := by
    by_cases hf : AEStronglyMeasurable f μ
    · have hg : ¬ AEStronglyMeasurable g μ := fun hg => hfg ⟨hf, hg⟩
      exact Or.inr (eLpNorm_of_not_aestronglyMeasurable hg)
    · exact Or.inl (eLpNorm_of_not_aestronglyMeasurable hf)
  rcases eq_or_ne (c * eLpNorm f p μ * eLpNorm g q μ) 0 with H | H
  · have key : ∀ᵐ x ∂μ, c * ‖f x‖ₑ * ‖g x‖ₑ = 0 := by
      rcases mul_eq_zero.mp H with H' | H'
      · rcases mul_eq_zero.mp H' with H'' | H''
        · filter_upwards with x
          simp [H'']
        · have hf : AEStronglyMeasurable f μ := by
            by_contra hf
            rw [eLpNorm_of_not_aestronglyMeasurable hf] at H''
            exact ENNReal.top_ne_zero H''
          have hf0 : f =ᵐ[μ] 0 := by
            first
              | exact (eLpNorm_eq_zero_iff hf hp).mp H''
              | exact (eLpNorm_eq_zero_iff hp).mp H''
          filter_upwards [hf0] with x hx
          simp [hx]
      · have hg : AEStronglyMeasurable g μ := by
          by_contra hg
          rw [eLpNorm_of_not_aestronglyMeasurable hg] at H'
          exact ENNReal.top_ne_zero H'
        have hg0 : g =ᵐ[μ] 0 := by
          first
            | exact (eLpNorm_eq_zero_iff hg hq).mp H'
            | exact (eLpNorm_eq_zero_iff hq).mp H'
        filter_upwards [hg0] with x hx
        simp [hx]
    have key2 : (fun x => b (f x) (g x)) =ᵐ[μ] 0 := by
      filter_upwards [h, key] with x hx hx'
      have hx2 := hx.trans_eq hx'
      simpa using hx2
    rw [eLpNorm_congr_ae key2]
    simp
  · have h1 := mul_ne_zero_iff.mp H
    have h2 := mul_ne_zero_iff.mp h1.1
    rcases H1 with H1 | H1
    · first
        | (rw [H1, ENNReal.mul_top h2.1, ENNReal.top_mul h1.2]; exact le_top)
        | simp [H1, h1.1, h1.2, h2.1, h2.2]
    · first
        | (rw [H1, ENNReal.mul_top h1.1]; exact le_top)
        | simp [H1, h1.1, h1.2, h2.1, h2.2]
