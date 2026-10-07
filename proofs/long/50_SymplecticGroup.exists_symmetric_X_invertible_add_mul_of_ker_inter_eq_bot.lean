/-
Machine-generated proof, verified by Lean.

Theorem:      SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/SymplecticGroup.lean, line 255
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  48 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  have hker' : ∀ x : l → R, A *ᵥ x = 0 → C *ᵥ x = 0 → x = 0 := by
    first
      | exact hker
      | exact fun x h1 h2 ↦ hker x (by simpa using h1) (by simpa using h2)
  suffices H : ∀ (k : ℕ) (A : Matrix l l R), (∀ x : l → R, A *ᵥ x = 0 → C *ᵥ x = 0 → x = 0) →
      Aᵀ * C = Cᵀ * A → Module.finrank R (LinearMap.ker A.mulVecLin) = k →
      ∃ X : Matrix l l R, X.IsSymm ∧ IsUnit (A + X * C) by
    exact H _ A hker' hsymm rfl
  intro k
  first
    | refine Nat.strong_induction_on k ?_
    | refine Nat.strongRecOn k ?_
  intro k ih A hkerA hsymmA hk
  by_cases hinj : Function.Injective A.mulVec
  · refine ⟨0, Matrix.isSymm_zero, ?_⟩
    rw [Matrix.zero_mul, add_zero]
    first
      | exact Matrix.mulVec_injective_iff_isUnit.1 hinj
      | rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro hdet
        obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
        exact hv (hinj (by rw [hAv, Matrix.mulVec_zero]))
  obtain ⟨x₀, hx₀, hAx₀⟩ : ∃ x₀ : l → R, x₀ ≠ 0 ∧ A *ᵥ x₀ = 0 := by
    by_contra hcon
    push_neg at hcon
    apply hinj
    intro x y hxy
    by_contra hne
    exact hcon (x - y) (sub_ne_zero.2 hne) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  have hCx₀ : C *ᵥ x₀ ≠ 0 := fun h ↦ hx₀ (hkerA x₀ hAx₀ h)
  obtain ⟨i, hi⟩ : ∃ i, (C *ᵥ x₀) i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hCx₀ (funext hcon)
  obtain ⟨E, hEsymm, hEt, hEw⟩ : ∃ E : Matrix l l R, E.IsSymm ∧ Eᵀ = E ∧
      ∀ w : l → R, E *ᵥ w = Pi.single i (w i) := by
    refine ⟨Matrix.diagonal (Pi.single i 1), Matrix.isSymm_diagonal _,
      Matrix.diagonal_transpose _, fun w ↦ ?_⟩
    ext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have hpair : ∀ v w : l → R, (C *ᵥ v) ⬝ᵥ (A *ᵥ w) = (A *ᵥ v) ⬝ᵥ (C *ᵥ w) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hsymmA]
  have hsub : ∀ x : l → R, (A + E * C) *ᵥ x = 0 → A *ᵥ x = 0 := by
    intro x hx
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hEw] at hx
    have hAx : A *ᵥ x = -Pi.single i ((C *ᵥ x) i) := eq_neg_of_add_eq_zero_left hx
    have h1 := hpair x₀ x
    have h2 : (C *ᵥ x) i = 0 := by
      simpa [hAx₀, hAx, hi] using h1
    rw [hAx, h2]
    simp
  have hx₀' : (A + E * C) *ᵥ x₀ ≠ 0 := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hEw, hAx₀, zero_add]
    intro h
    apply hi
    simpa using congrFun h i
  have hkerA' : ∀ x : l → R, (A + E * C) *ᵥ x = 0 → C *ᵥ x = 0 → x = 0 := by
    intro x h1 h2
    refine hkerA x ?_ h2
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero, add_zero] at h1
    exact h1
  have hsymmA' : (A + E * C)ᵀ * C = Cᵀ * (A + E * C) := by
    rw [Matrix.transpose_add, Matrix.transpose_mul, hEt, Matrix.add_mul, Matrix.mul_add, hsymmA,
      Matrix.mul_assoc]
  have hlt : LinearMap.ker (A + E * C).mulVecLin < LinearMap.ker A.mulVecLin := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun x hx ↦ ?_, x₀, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      exact hsub x hx
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hAx₀
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hx₀'
  have hk' : Module.finrank R (LinearMap.ker (A + E * C).mulVecLin) < k := by
    rw [← hk]
    first
      | exact Submodule.finrank_lt_finrank_of_lt hlt
      | exact Submodule.finrank_strictMono hlt
  obtain ⟨X', hX'symm, hX'unit⟩ := ih _ hk' (A + E * C) hkerA' hsymmA' rfl
  refine ⟨E + X', hEsymm.add hX'symm, ?_⟩
  rw [Matrix.add_mul, ← add_assoc]
  exact hX'unit
