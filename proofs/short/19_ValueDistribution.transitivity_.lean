/-
Machine-generated proof, verified by Lean.

Theorem:      ValueDistribution.transitivity₂
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean, line 190
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma transitivity₂ {f₁ f₂ f₃ : ℂ → ℂ} (h₂₃ : f₂ =ᶠ[codiscrete ℂ] f₃)
    (h₁₂ : (characteristic f₁ ⊤ - characteristic f₂ ⊤) =O[atTop] (1 : ℝ → ℝ)) :
    (characteristic f₁ ⊤ - characteristic f₃ ⊤) =O[atTop] (1 : ℝ → ℝ) := by
  have key : ∀ r : ℝ, r ≠ 0 → characteristic f₂ ⊤ r = characteristic f₃ ⊤ r := by
    intro r hr
    first
    | exact characteristic_congr_codiscrete h₂₃ hr
    | exact characteristic_congr_codiscrete hr h₂₃
    | (have hp : proximity f₂ ⊤ r = proximity f₃ ⊤ r := by
         first
         | exact proximity_congr_codiscrete h₂₃ hr
         | exact proximity_congr_codiscrete hr h₂₃
         | (have hsub : f₂ =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] f₃ :=
              h₂₃.filter_mono (codiscreteWithin.mono (Set.subset_univ _))
            have hs : (fun z ↦ log⁺ ‖f₂ z‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
                (fun z ↦ log⁺ ‖f₃ z‖) := by
              filter_upwards [hsub] with z hz
              simp only [hz]
            first
            | (simp only [proximity_top]
               exact circleAverage_congr_codiscreteWithin hs hr)
            | (simp only [proximity, reduceDIte]
               exact circleAverage_congr_codiscreteWithin hs hr))
         | (have hsub : f₂ =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] f₃ := by
              have h0 : {z | f₂ z = f₃ z} ∈ codiscreteWithin (Set.univ : Set ℂ) := h₂₃
              rw [mem_codiscreteWithin] at h0
              show {z | f₂ z = f₃ z} ∈ codiscreteWithin (sphere (0 : ℂ) |r|)
              rw [mem_codiscreteWithin]
              intro x _
              exact (h0 x (Set.mem_univ x)).mono_right
                (Filter.principal_mono.mpr fun y hy ↦ ⟨Set.mem_univ y, hy.2⟩)
            have hs : (fun z ↦ log⁺ ‖f₂ z‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
                (fun z ↦ log⁺ ‖f₃ z‖) := by
              filter_upwards [hsub] with z hz
              simp only [hz]
            first
            | (simp only [proximity_top]
               exact circleAverage_congr_codiscreteWithin hs hr)
            | (simp only [proximity, reduceDIte]
               exact circleAverage_congr_codiscreteWithin hs hr))
       have hd : divisor f₂ Set.univ = divisor f₃ Set.univ := by
         by_cases hm : MeromorphicOn f₂ Set.univ
         · first
           | exact divisor_congr_codiscreteWithin hm h₂₃ isOpen_univ
           | exact divisor_congr_codiscreteWithin_of_eqOn_compl hm h₂₃ (by simp)
         · have hm' : ¬ MeromorphicOn f₃ Set.univ := by
             intro h
             apply hm
             first
             | exact h.congr_codiscreteWithin h₂₃.symm isOpen_univ
             | exact h.congr_codiscreteWithin_of_eqOn_compl h₂₃.symm (by simp)
           ext z
           first
           | (simp [divisor_def, hm, hm']; done)
           | (simp [divisor, hm, hm']; done)
           | (simp [hm, hm']; done)
       have hc : logCounting f₂ ⊤ = logCounting f₃ ⊤ := by
         first
         | exact logCounting_congr_codiscrete h₂₃
         | (simp only [logCounting_top, hd]; done)
         | (simp only [logCounting, reduceDIte, hd]; done)
         | (rw [logCounting_top, logCounting_top, hd])
       simp only [characteristic, Pi.add_apply, hp, hc])
  have hEq : (characteristic f₁ ⊤ - characteristic f₂ ⊤) =ᶠ[atTop]
      (characteristic f₁ ⊤ - characteristic f₃ ⊤) := by
    filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with r hr
    simp only [Pi.sub_apply, key r hr]
  exact h₁₂.congr' hEq (Filter.EventuallyEq.refl _ _)
