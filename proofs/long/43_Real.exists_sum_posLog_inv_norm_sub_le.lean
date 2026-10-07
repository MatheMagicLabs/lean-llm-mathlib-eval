/-
Machine-generated proof, verified by Lean.

Theorem:      Real.exists_sum_posLog_inv_norm_sub_le
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/SecondMainTheorem.lean, line 56
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  67 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_sum_posLog_inv_norm_sub_le (s : Finset 𝕜) :
    ∃ C, ∀ w : 𝕜, ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ + C := by
  classical
  have hpl : ∀ x : ℝ, 0 ≤ log⁺ x := fun x => by
    first
      | exact posLog_nonneg
      | exact posLog_nonneg x
      | exact le_max_left _ _
  have aux : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → log⁺ (A + B) ≤ log 2 + log⁺ A + log⁺ B := by
    intro A B hA hB
    first
      | exact posLog_add
      | exact le_trans posLog_add (le_of_eq (by ring))
      | exact le_trans (posLog_add _ _) (le_of_eq (by ring))
      | (show max 0 (log (A + B)) ≤ log 2 + max 0 (log A) + max 0 (log B)
         have h0A := le_max_left 0 (log A)
         have h0B := le_max_left 0 (log B)
         have h1A := le_max_right 0 (log A)
         have h1B := le_max_right 0 (log B)
         have hl2 : 0 ≤ log 2 := log_nonneg (by norm_num)
         refine max_le (by linarith) ?_
         rcases (add_nonneg hA hB).eq_or_lt with h | h
         · rw [← h, log_zero]
           linarith
         · rcases le_total A B with hAB | hAB
           · have hBpos : 0 < B := by linarith
             have h2 : log (A + B) ≤ log (2 * B) := log_le_log h (by linarith)
             rw [log_mul (by norm_num) hBpos.ne'] at h2
             linarith
           · have hApos : 0 < A := by linarith
             have h2 : log (A + B) ≤ log (2 * A) := log_le_log h (by linarith)
             rw [log_mul (by norm_num) hApos.ne'] at h2
             linarith)
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℝ, 0 < c ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 2 * c ≤ ‖a - b‖ := by
    by_cases hne : s.offDiag.Nonempty
    · obtain ⟨p, hp, hmin⟩ := s.offDiag.exists_min_image (fun p => ‖p.1 - p.2‖) hne
      rw [Finset.mem_offDiag] at hp
      have hpos : 0 < ‖p.1 - p.2‖ := by
        first
          | exact norm_pos_iff.2 (sub_ne_zero.2 hp.2.2)
          | exact norm_pos_iff.mpr (sub_ne_zero.mpr hp.2.2)
          | simpa [sub_eq_zero] using hp.2.2
      refine ⟨‖p.1 - p.2‖ / 2, half_pos hpos, fun a ha b hb hab => ?_⟩
      have h1 : ‖p.1 - p.2‖ ≤ ‖a - b‖ := hmin (a, b) (Finset.mem_offDiag.2 ⟨ha, hb, hab⟩)
      linarith
    · exact ⟨1, one_pos, fun a ha b hb hab =>
        (hne ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩⟩).elim⟩
  refine ⟨log 2 + log⁺ (#s * c⁻¹) + #s * log⁺ c⁻¹, fun w => ?_⟩
  have hlog2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hP1 := hpl (‖∑ a ∈ s, (w - a)⁻¹‖)
  have hP2 := hpl ((#s : ℝ) * c⁻¹)
  have hP3 := hpl (c⁻¹)
  by_cases hnear : ∃ a ∈ s, ‖w - a‖ < c
  · obtain ⟨a₀, ha₀, hwa₀⟩ := hnear
    have key : ∀ a ∈ s.erase a₀, c ≤ ‖w - a‖ := by
      intro a ha
      rw [Finset.mem_erase] at ha
      have h1 := hcs a₀ ha₀ a ha.2 (Ne.symm ha.1)
      have h2 : ‖a₀ - a‖ ≤ ‖a₀ - w‖ + ‖w - a‖ := by
        calc ‖a₀ - a‖ = ‖(a₀ - w) + (w - a)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖a₀ - w‖ + ‖w - a‖ := norm_add_le _ _
      have h3 : ‖a₀ - w‖ = ‖w - a₀‖ := norm_sub_rev a₀ w
      linarith
    have e1 : ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ = log⁺ ‖w - a₀‖⁻¹ + ∑ a ∈ s.erase a₀, log⁺ ‖w - a‖⁻¹ :=
      (Finset.add_sum_erase s (fun a => log⁺ ‖w - a‖⁻¹) ha₀).symm
    have e2 : ∑ a ∈ s, (w - a)⁻¹ = (w - a₀)⁻¹ + ∑ a ∈ s.erase a₀, (w - a)⁻¹ :=
      (Finset.add_sum_erase s (fun a => (w - a)⁻¹) ha₀).symm
    have hcard : ((#(s.erase a₀) : ℕ) : ℝ) ≤ (#s : ℝ) := by
      exact_mod_cast Finset.card_erase_le
    have e3 : ∑ a ∈ s.erase a₀, log⁺ ‖w - a‖⁻¹ ≤ (#(s.erase a₀) : ℝ) * log⁺ c⁻¹ :=
      sum_posLog_inv_norm_sub_le hc key
    have e4 : (#(s.erase a₀) : ℝ) * log⁺ c⁻¹ ≤ (#s : ℝ) * log⁺ c⁻¹ :=
      mul_le_mul_of_nonneg_right hcard hP3
    have e5 : ‖∑ a ∈ s.erase a₀, (w - a)⁻¹‖ ≤ (#s : ℝ) * c⁻¹ := by
      calc ‖∑ a ∈ s.erase a₀, (w - a)⁻¹‖ ≤ ∑ a ∈ s.erase a₀, ‖(w - a)⁻¹‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ s.erase a₀, c⁻¹ := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_inv]
          gcongr
          exact key a ha
        _ = (#(s.erase a₀) : ℝ) * c⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (#s : ℝ) * c⁻¹ := mul_le_mul_of_nonneg_right hcard (inv_nonneg.2 hc.le)
    have e6 : ‖w - a₀‖⁻¹ ≤ ‖∑ a ∈ s, (w - a)⁻¹‖ + (#s : ℝ) * c⁻¹ := by
      have h : (w - a₀)⁻¹ = ∑ a ∈ s, (w - a)⁻¹ - ∑ a ∈ s.erase a₀, (w - a)⁻¹ := by
        rw [e2]
        ring
      have h' : ‖(w - a₀)⁻¹‖ ≤ ‖∑ a ∈ s, (w - a)⁻¹‖ + ‖∑ a ∈ s.erase a₀, (w - a)⁻¹‖ := by
        rw [h]
        exact norm_sub_le _ _
      rw [norm_inv] at h'
      linarith
    have hx0 : (0 : ℝ) ≤ ‖w - a₀‖⁻¹ := by positivity
    have e7 : log⁺ ‖w - a₀‖⁻¹ ≤ log⁺ (‖∑ a ∈ s, (w - a)⁻¹‖ + (#s : ℝ) * c⁻¹) := by
      first
        | exact posLog_le_posLog (le_trans (by norm_num) hx0) e6
        | exact posLog_le_posLog hx0 e6
        | exact posLog_le_posLog (by linarith) e6
    have e8 := aux (‖∑ a ∈ s, (w - a)⁻¹‖) ((#s : ℝ) * c⁻¹) (norm_nonneg _) (by positivity)
    linarith
  · have hfar : ∀ a ∈ s, c ≤ ‖w - a‖ := fun a ha => not_lt.1 fun h => hnear ⟨a, ha, h⟩
    have h1 := sum_posLog_inv_norm_sub_le hc hfar
    linarith
