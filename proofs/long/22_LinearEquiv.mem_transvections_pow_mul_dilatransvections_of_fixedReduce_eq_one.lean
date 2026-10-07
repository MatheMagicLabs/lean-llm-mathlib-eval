/-
Machine-generated proof, verified by Lean.

Theorem:      LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_fixedReduce_eq_one
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 217
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  37 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem mem_transvections_pow_mul_dilatransvections_of_fixedReduce_eq_one
    {e : V ≃ₗ[K] V} (he : e.fixedReduce = 1) :
    e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V := by
  have hfix : ∀ v : V, e v - v ∈ e.fixedSubmodule := by
    intro v
    have h1 := DFunLike.congr_fun he (Submodule.Quotient.mk v)
    rw [← Submodule.Quotient.eq]
    first
      | exact h1
      | simpa [fixedReduce] using h1
      | simpa using h1
  have hD : ∀ φ : V ≃ₗ[K] V, finrank K (V ⧸ φ.fixedSubmodule) ≤ 1 →
      φ ∈ dilatransvections K V := by
    intro φ h
    first
      | rw [fixedSubmodule_eq_ker, (LinearMap.quotKerEquivRange _).finrank_eq] at h
        simpa [← mem_dilatransvections_iff_finrank] using h
      | rw [mem_dilatransvections_iff_finrank]
        refine le_trans (le_of_eq ?_) h
        rw [fixedSubmodule_eq_ker]
        exact (LinearMap.quotKerEquivRange _).finrank_eq.symm
  have key : ∀ n : ℕ, ∀ φ : V ≃ₗ[K] V, (∀ v : V, φ v - v ∈ φ.fixedSubmodule) →
      finrank K (V ⧸ φ.fixedSubmodule) = n →
      φ ∈ transvections K V ^ (n - 1) * dilatransvections K V := by
    intro n
    induction n with
    | zero =>
      intro φ _ hn
      show φ ∈ transvections K V ^ 0 * dilatransvections K V
      rw [pow_zero, one_mul]
      exact hD φ (by omega)
    | succ n ih =>
      intro φ hφ hn
      by_cases hn0 : n = 0
      · subst hn0
        show φ ∈ transvections K V ^ 0 * dilatransvections K V
        rw [pow_zero, one_mul]
        exact hD φ (by omega)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨u, hu⟩ : ∃ u : V, u ∉ φ.fixedSubmodule := by
        by_contra hcon
        push_neg at hcon
        have htop : φ.fixedSubmodule = ⊤ := eq_top_iff.2 fun x _ ↦ hcon x
        have h1 := Submodule.finrank_quotient_add_finrank φ.fixedSubmodule
        rw [htop, finrank_top] at h1
        rw [htop] at hn
        omega
      obtain ⟨f, hfu, hfker⟩ : ∃ f : Module.Dual K V, f u = 1 ∧
          ∀ x ∈ φ.fixedSubmodule, f x = 0 := by
        have hu0 : (Submodule.Quotient.mk u : V ⧸ φ.fixedSubmodule) ≠ 0 := by
          rw [ne_eq, Submodule.Quotient.mk_eq_zero]
          exact hu
        have hinj : LinearMap.ker (LinearMap.toSpanSingleton K (V ⧸ φ.fixedSubmodule)
            (Submodule.Quotient.mk u)) = ⊥ := by
          rw [LinearMap.ker_eq_bot']
          intro c hc
          rw [LinearMap.toSpanSingleton_apply] at hc
          first
            | exact (smul_eq_zero.1 hc).resolve_right hu0
            | by_contra hc0
              apply hu0
              rw [← one_smul K (Submodule.Quotient.mk u : V ⧸ φ.fixedSubmodule),
                ← inv_mul_cancel₀ hc0, mul_smul, hc, smul_zero]
        obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
        have hgu : g (Submodule.Quotient.mk u) = 1 := by
          have h1 := LinearMap.congr_fun hg 1
          simpa using h1
        refine ⟨g ∘ₗ φ.fixedSubmodule.mkQ, ?_, fun x hx ↦ ?_⟩
        · simpa using hgu
        · have hx0 : (Submodule.Quotient.mk x : V ⧸ φ.fixedSubmodule) = 0 := by
            rw [Submodule.Quotient.mk_eq_zero]
            exact hx
          simp [hx0]
      have hf : φ.fixedSubmodule ⊔ K ∙ (φ u - u) ≤ LinearMap.ker f := by
        rw [sup_le_iff, Submodule.span_singleton_le_iff_mem]
        exact ⟨fun x hx ↦ LinearMap.mem_ker.2 (hfker x hx),
          LinearMap.mem_ker.2 (hfker _ (hφ u))⟩
      have hs : f (φ u - u) = 0 := hfker _ (hφ u)
      have hfeu : f (φ u) = 1 := by
        have h := hs
        rw [map_sub, sub_eq_zero, hfu] at h
        exact h
      have h3 : f (u - φ u) = 0 := by
        rw [map_sub, hfu, hfeu, sub_self]
      have hu' : u - φ u ∈ φ.fixedSubmodule := by
        rw [← neg_sub]
        exact neg_mem (hφ u)
      have h1 : ∀ y, auxTransvection hf y = y + f y • (u - φ u) := by
        intro y
        first
          | (simp [auxTransvection, LinearMap.transvection.apply]; done)
          | rfl
      have h2 : ∀ y, LinearEquiv.transvection hs y = y + f y • (φ u - u) := by
        intro y
        first
          | (simp [LinearMap.transvection.apply]; done)
          | rfl
      have hst : LinearEquiv.transvection hs * auxTransvection hf = 1 := by
        ext x
        show LinearEquiv.transvection hs (auxTransvection hf x) = x
        have h7 : f (f x • (u - φ u)) = 0 := by
          have h8 : u - φ u ∈ LinearMap.ker f := LinearMap.mem_ker.mpr h3
          first
            | exact LinearMap.mem_ker.mp (Submodule.smul_mem _ (f x) h8)
            | simp [h3]
        rw [h1, h2, map_add, h7, add_zero]
        first
          | rw [← neg_sub u (φ u), smul_neg, add_neg_cancel_right]
          | rw [add_assoc, ← smul_add, sub_add_sub_cancel, sub_self, smul_zero, add_zero]
          | simp
      have hprod : LinearEquiv.transvection hs * (auxTransvection hf * φ) = φ := by
        rw [← mul_assoc, hst, one_mul]
      have hs_mem : LinearEquiv.transvection hs ∈ transvections K V := by
        first
          | exact transvection_mem_transvections hs
          | exact LinearEquiv.transvection_mem_transvections hs
          | exact ⟨f, _, hs, rfl⟩
          | exact ⟨_, f, hs, rfl⟩
          | exact ⟨f, φ u - u, hs, rfl⟩
          | exact ⟨⟨(f, φ u - u), hs⟩, rfl⟩
          | exact ⟨⟨f, φ u - u⟩, hs, rfl⟩
          | (simp only [transvections, Set.mem_setOf_eq]; exact ⟨f, _, hs, rfl⟩)
      have hφ' : ∀ v : V, (auxTransvection hf * φ) v - v ∈
          (auxTransvection hf * φ).fixedSubmodule := by
        intro v
        rw [auxTransvection_mul_fixed (hf := hf) hfu]
        apply Submodule.mem_sup_left
        rw [LinearEquiv.mul_apply, h1, add_sub_right_comm]
        exact add_mem (hφ v) (Submodule.smul_mem _ _ hu')
      have hn' : finrank K (V ⧸ (auxTransvection hf * φ).fixedSubmodule) = m + 1 := by
        have h4 := finrank_mod_auxTransvection_mul_fixed (hf := hf) hfu hu
        omega
      have hmem := ih (auxTransvection hf * φ) hφ' hn'
      rw [show m + 1 - 1 = m by omega] at hmem
      rw [show m + 1 + 1 - 1 = m + 1 by omega, pow_succ', mul_assoc, ← hprod]
      exact Set.mul_mem_mul hs_mem hmem
  exact key _ e hfix rfl
