/-
Machine-generated proof, verified by Lean.

Theorem:      ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/CStarAlgebra/PositiveLinearFunctional.lean, line 115
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  11 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem monotone_iff_tendsto_nhds_opNorm {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Monotone f ↔ l.Tendsto (f ·) (𝓝 ‖f‖) := by
  constructor
  · intro hmono
    first
    | exact PositiveContinuousLinearMap.tendsto_nhds_opNorm { f with monotone' := hmono } hl
    | exact PositiveContinuousLinearMap.tendsto_nhds_opNorm ⟨⟨f.toLinearMap, hmono⟩, f.cont⟩ hl
  · intro h
    have hne : l.NeBot := hl.neBot
    have hconj : ∀ x c : A, 0 ≤ x → 0 ≤ star c * x * c := by
      intro x c hx
      first
      | exact star_left_conjugate_nonneg hx c
      | (rw [StarOrderedRing.nonneg_iff] at hx
         induction hx using AddSubmonoid.closure_induction with
         | mem y hy =>
           obtain ⟨t, rfl⟩ := hy
           calc (0 : A) ≤ star (t * c) * (t * c) := star_mul_self_nonneg _
             _ = star c * (star t * t) * c := by rw [star_mul]; simp only [mul_assoc]
         | zero => simp
         | add y z _ _ hy hz =>
           rw [mul_add, add_mul]
           exact add_nonneg hy hz)
    have key : ∀ a : A, 0 ≤ a → a * a ≤ a → 0 ≤ (f a).re := by
      intro a ha0 h1
      have haa : star a = a := ha0.star_eq
      have hnorm : ∀ e : A, 0 ≤ e → ‖e‖ ≤ 1 → ‖e - a * e‖ ≤ 1 := by
        intro e he0 he1
        have hee : star e = e := he0.star_eq
        have hkey : e * e - star (e - a * e) * (e - a * e) =
            star e * a * e + star e * (a - a * a) * e := by
          rw [star_sub, star_mul, hee, haa]
          simp only [mul_sub, sub_mul, mul_assoc]
          abel
        have hle : star (e - a * e) * (e - a * e) ≤ e * e := by
          rw [← sub_nonneg, hkey]
          exact add_nonneg (hconj a e ha0) (hconj (a - a * a) e (sub_nonneg.mpr h1))
        have h4 : ‖star (e - a * e) * (e - a * e)‖ ≤ ‖e * e‖ := by
          first
          | exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (star_mul_self_nonneg _)
          | exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
          | exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg _) hle
          | exact norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg _) hle
        rw [CStarRing.norm_star_mul_self] at h4
        have h5 : ‖e * e‖ ≤ ‖e‖ * ‖e‖ := norm_mul_le e e
        nlinarith [norm_nonneg e, norm_nonneg (e - a * e)]
      have h2 : Tendsto (fun e ↦ f (a * e)) l (𝓝 (f a)) := by
        first
        | exact (f.continuous.tendsto a).comp (hl.tendsto_mul_left a)
        | exact ((map_continuous f).tendsto a).comp (hl.tendsto_mul_left a)
        | exact (ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_left a)
      have hlim : Tendsto (fun e ↦ f (e - a * e)) l (𝓝 ((‖f‖ : ℂ) - f a)) := by
        first
        | simpa only [map_sub] using h.sub h2
        | exact (h.sub h2).congr (fun e => (map_sub f e (a * e)).symm)
      have hbound : ‖(‖f‖ : ℂ) - f a‖ ≤ ‖f‖ := by
        refine le_of_tendsto hlim.norm ?_
        filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he0 he1
        calc ‖f (e - a * e)‖ ≤ ‖f‖ * ‖e - a * e‖ := f.le_opNorm _
          _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg _) (hnorm e he0 he1)
      have hre : ((‖f‖ : ℂ) - f a).re ≤ ‖f‖ := by
        first
        | exact (Complex.re_le_norm _).trans hbound
        | exact (RCLike.re_le_norm _).trans hbound
        | exact (Complex.re_le_abs _).trans hbound
        | exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hbound
      simp only [Complex.sub_re, Complex.ofReal_re] at hre
      linarith
    have hstar : ∀ s : A, 0 ≤ (f (star s * s)).re := by
      intro s
      obtain ⟨r, hr0, hrs⟩ : ∃ r : ℝ, 0 < r ∧ r * ‖s‖ ≤ 1 := by
        have hpos : (0 : ℝ) < ‖s‖ + 1 := by positivity
        refine ⟨(‖s‖ + 1)⁻¹, inv_pos.mpr hpos, ?_⟩
        calc (‖s‖ + 1)⁻¹ * ‖s‖ ≤ (‖s‖ + 1)⁻¹ * (‖s‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (inv_pos.mpr hpos).le
          _ = 1 := inv_mul_cancel₀ hpos.ne'
      have hnr : ‖(r : ℂ)‖ = r := by
        first
        | exact Complex.norm_of_nonneg hr0.le
        | (rw [Complex.norm_real, Real.norm_of_nonneg hr0.le])
        | (simp [hr0.le]; done)
        | (simp [abs_of_pos hr0]; done)
      have hxn : ‖(r : ℂ) • s‖ ≤ 1 := by
        rw [norm_smul, hnr]
        exact hrs
      have hb0 : 0 ≤ star ((r : ℂ) • s) * ((r : ℂ) • s) := star_mul_self_nonneg _
      have hb1 : ‖star ((r : ℂ) • s) * ((r : ℂ) • s)‖ ≤ 1 := by
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg ((r : ℂ) • s)]
      have hb := key _ hb0 (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hb0 hb1)
      have hst : star (r : ℂ) = (r : ℂ) := by
        first
        | exact Complex.conj_ofReal r
        | (simp; done)
        | (simpa using Complex.conj_ofReal r)
        | exact Complex.ext (by simp) (by simp)
      have heq : star ((r : ℂ) • s) * ((r : ℂ) • s) = ((r : ℂ) * (r : ℂ)) • (star s * s) := by
        rw [star_smul, hst]
        first
        | (rw [smul_mul_smul_comm]; done)
        | (rw [smul_mul_smul]; done)
        | (simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; done)
      rw [heq] at hb
      simp only [map_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hb
      nlinarith [mul_pos hr0 hr0]
    have hpos : ∀ a : A, 0 ≤ a → 0 ≤ f a := by
      intro a ha
      have hre : 0 ≤ (f a).re := by
        rw [StarOrderedRing.nonneg_iff] at ha
        induction ha using AddSubmonoid.closure_induction with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          exact hstar s
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, Complex.add_re]
          exact add_nonneg hx hy
      have him : (f a).im = 0 := by
        first
        | exact im_apply_eq_zero_of_tendsto_nhds_opNorm hl h (IsSelfAdjoint.of_nonneg ha)
        | exact im_apply_eq_zero_of_tendsto_nhds_opNorm hl h ha.isSelfAdjoint
      refine Complex.le_def.mpr ⟨?_, ?_⟩
      · simpa using hre
      · simp [him]
    intro a b hab
    have hab' := hpos (b - a) (sub_nonneg.mpr hab)
    rwa [map_sub, sub_nonneg] at hab'
