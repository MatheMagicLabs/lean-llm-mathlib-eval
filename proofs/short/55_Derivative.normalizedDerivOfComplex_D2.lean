/-
Machine-generated proof, verified by Lean.

Theorem:      Derivative.normalizedDerivOfComplex_D2
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/ModularForms/RamanujanFormula.lean, line 72
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  7 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma normalizedDerivOfComplex_D2 (γ : SL(2, ℤ)) :
    D (D2 γ) = fun z : ℍ ↦ -(γ 1 0 : ℂ) ^ 2 / denom γ z ^ 2 := by
  funext z
  have hden : ∀ w : ℍ, denom γ w = (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ) := by
    intro w
    first
      | exact ModularGroup.denom_apply γ w
      | exact UpperHalfPlane.denom_apply γ w
      | simp [denom]
      | (simp only [denom]; norm_cast)
      | rfl
  have hne : (γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    rw [← hden z]
    first
      | exact denom_ne_zero γ z
      | exact denom_ne_zero _ z
      | exact UpperHalfPlane.denom_ne_zero _ z
  have hev : (D2 γ ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      fun w : ℂ ↦ 2 * π * I * (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos]
      with w hw
    have hw' : ((ofComplex w : ℍ) : ℂ) = w := by
      first
        | simp [ofComplex_apply_of_im_pos hw]
        | (rw [ofComplex_apply_of_im_pos hw]; rfl)
    have h1 := hden (ofComplex w)
    rw [hw'] at h1
    simp only [Function.comp_apply, D2, hw', h1, div_eq_mul_inv]
    try ring
  have hderiv : HasDerivAt
      (fun w : ℂ ↦ 2 * π * I * (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))⁻¹)
      (2 * π * I * (γ 1 0 : ℂ) *
        (-((γ 1 0 : ℂ) * 1) / ((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)) ^ 2)) (z : ℂ) :=
    ((((hasDerivAt_id (z : ℂ)).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)).inv hne).const_mul _
  have hD : deriv (D2 γ ∘ ofComplex) (z : ℂ) = 2 * π * I * (γ 1 0 : ℂ) *
      (-((γ 1 0 : ℂ) * 1) / ((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)) ^ 2) :=
    hev.deriv_eq.trans hderiv.deriv
  have hc : (2 * π * I : ℂ) ≠ 0 := by
    first
      | exact two_pi_I_ne_zero
      | exact Complex.two_pi_I_ne_zero
      | simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hDz : D (D2 γ) z = (2 * π * I)⁻¹ * deriv (D2 γ ∘ ofComplex) (z : ℂ) := by
    first
      | rfl
      | (simp only [normalizedDerivOfComplex, smul_eq_mul]; done)
      | (simp only [normalizedDerivOfComplex, smul_eq_mul, Function.comp_def]; done)
      | (simp only [normalizedDerivOfComplex, smul_eq_mul]; ring1)
      | (unfold normalizedDerivOfComplex; ring1)
  refine hDz.trans ?_
  rw [hD, hden z]
  first
    | (rw [mul_assoc (2 * (π : ℂ) * I), inv_mul_cancel_left₀ hc]; ring1)
    | (rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]; ring1)
    | (field_simp; ring1)
    | (field_simp; done)
