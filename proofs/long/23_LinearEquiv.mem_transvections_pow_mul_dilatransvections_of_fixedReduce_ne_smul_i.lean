/-
Machine-generated proof, verified by Lean.

Theorem:      LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_fixedReduce_ne_smul_id
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 417
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  41 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem mem_transvections_pow_mul_dilatransvections_of_fixedReduce_ne_smul_id
    {e : V ≃ₗ[K] V}
    (he : ∀ a : K, ∃ x, e.fixedReduce x ≠ a • x) :
    e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V := by
  induction h : finrank K (V ⧸ e.fixedSubmodule) generalizing e he with
  | zero => simp [mem_dilatransvections_iff_finrank_quotient, h]
  | succ n hind =>
    match n with
    | 0 => simp [mem_dilatransvections_iff_finrank_quotient, h]
    | n + 1 =>
      simp only [add_tsub_cancel_right] at hind
      have hgoal : ∀ t : V ≃ₗ[K] V, t ∈ transvections K V →
          t * e ∈ transvections K V ^ n * dilatransvections K V →
          e ∈ transvections K V ^ (n + 1 + 1 - 1) * dilatransvections K V := by
        intro t ht hte
        have h1 : t⁻¹ ∈ transvections K V := by rwa [inv_mem_transvections_iff]
        have h2 := Set.mul_mem_mul h1 hte
        rw [inv_mul_cancel_left] at h2
        rw [add_tsub_cancel_right, pow_succ', mul_assoc]
        exact h2
      obtain ⟨f, v, hv, hf, hfv⟩ := exists_dual_of_fixedReduce_ne_smul he (by omega)
      have hv_notMem : v ∉ e.fixedSubmodule := fun hv' ↦ by
        apply one_ne_zero' K
        rw [← hfv, ← LinearMap.mem_ker]
        exact hf (mem_sup_left hv')
      have hfin : ∀ (f' : Dual K V) (hf' : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker f'),
          f' v = 1 → finrank K (V ⧸ (auxTransvection hf' * e).fixedSubmodule) = n + 1 := by
        intro f' hf' hf'v
        have := finrank_mod_auxTransvection_mul_fixed (hf := hf') hf'v hv_notMem
        omega
      have hcase : ∀ (f' : Dual K V) (hf' : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker f'),
          f' v = 1 → (∀ a : K, ∃ x, (auxTransvection hf' * e).fixedReduce x ≠ a • x) →
          e ∈ transvections K V ^ (n + 1 + 1 - 1) * dilatransvections K V := by
        intro f' hf' hf'v hnh
        apply hgoal (auxTransvection hf')
        · apply mem_transvections
        · have hfin' := hfin f' hf' hf'v
          first
            | exact hind hnh hfin'
            | exact hind _ hnh hfin'
            | (apply hind <;> assumption)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        apply hgoal (auxTransvection hf)
        · apply mem_transvections
        · have h1 := hfin f hf hfv
          first
            | (rw [pow_zero, one_mul, mem_dilatransvections_iff_finrank_quotient]; omega)
            | simp [mem_dilatransvections_iff_finrank_quotient, h1]
      · by_cases H1 : ∀ a : K, ∃ x, (auxTransvection hf * e).fixedReduce x ≠ a • x
        · exact hcase f hf hfv H1
        · push_neg at H1
          obtain ⟨a, ha⟩ := H1
          have h3 := finrank_quotient_sup_span_singleton hv_notMem
          have h4 : 1 < finrank K (V ⧸ (e.fixedSubmodule ⊔ K ∙ v)) := by omega
          have hne_top : e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v < ⊤ := by
            first
              | (rw [sup_right_comm]; exact sup_span_singleton_lt_top (e v - v) h4)
              | exact (sup_right_comm _ _ _).trans_lt (sup_span_singleton_lt_top (e v - v) h4)
          obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt hne_top
          obtain ⟨g, hgu, hgW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
          have hgW' : e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v ≤ LinearMap.ker g := by
            rwa [LinearMap.le_ker_iff_map]
          have hg0 : g ≠ 0 := by
            intro hg
            apply hgu
            simp [hg]
          have hgv : g v = 0 := LinearMap.mem_ker.mp
            (hgW' (mem_sup_right (mem_span_singleton_self v)))
          have hfg : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker (f + g) := by
            intro x hx
            have h1 : f x = 0 := LinearMap.mem_ker.mp (hf hx)
            have h2 : g x = 0 := LinearMap.mem_ker.mp (hgW' (mem_sup_left hx))
            rw [LinearMap.mem_ker, LinearMap.add_apply, h1, h2, add_zero]
          have hfgv : (f + g) v = 1 := by
            rw [LinearMap.add_apply, hfv, hgv, add_zero]
          by_cases H2 : ∀ b : K, ∃ x, (auxTransvection hfg * e).fixedReduce x ≠ b • x
          · exact hcase (f + g) hfg hfgv H2
          · push_neg at H2
            obtain ⟨b, hb⟩ := H2
            exact (not_forall_fixedReduce_eq_smul hv hfv hfgv hg0 hne_top ha hb).elim
