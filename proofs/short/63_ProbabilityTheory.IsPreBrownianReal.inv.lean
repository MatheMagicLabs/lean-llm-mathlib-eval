/-
Machine-generated proof, verified by Lean.

Theorem:      ProbabilityTheory.IsPreBrownianReal.inv
Source:       Mathlib @ d0a050ad6, Mathlib/Probability/BrownianMotion/Basic.lean, line 277
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  12 tactic steps; area: Probability
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma IsPreBrownianReal.inv (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ t * (B (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · apply hB.isGaussianProcess.of_isGaussianProcess
    intro t
    exact ⟨{1 / t},
      { toFun x := t * x ⟨1 / t, Finset.mem_singleton_self _⟩
        map_add' x y := by
          first
          | (simp only [Pi.add_apply]; ring; done)
          | (simp [mul_add]; done)
          | (simp; ring; done)
        map_smul' c x := by
          first
          | (simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring; done)
          | (simp [mul_left_comm]; done)
          | (simp; ring; done) },
      by
        first
        | (simp; done)
        | (funext ω; simp; done)
        | (intro ω; simp; done)
        | rfl⟩
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval]
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · have hs' : 0 < s := by
        first
        | exact pos_iff_ne_zero.mpr hs
        | exact lt_of_le_of_ne (zero_le _) (Ne.symm hs)
      have ht : t ≠ 0 := (lt_of_lt_of_le hs' hst).ne'
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      have hmin : min (1 / s) (1 / t) = 1 / t := by
        first
        | exact min_eq_right (one_div_le_one_div_of_le hs' hst)
        | exact min_eq_right (by simpa [one_div] using inv_anti₀ hs' hst)
      rw [hmin]
      first
      | (simp [ht]; done)
      | (push_cast; field_simp; done)
      | (field_simp; done)
