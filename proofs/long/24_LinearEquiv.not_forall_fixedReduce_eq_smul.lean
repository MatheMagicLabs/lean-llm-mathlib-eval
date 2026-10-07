/-
Machine-generated proof, verified by Lean.

Theorem:      LinearEquiv.not_forall_fixedReduce_eq_smul
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 349
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  42 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private theorem not_forall_fixedReduce_eq_smul {f g : Dual K V} {v : V} {a b : K}
    (hv : LinearIndependent K
      ![e.fixedSubmodule.mkQ v, e.fixedReduce (e.fixedSubmodule.mkQ v)])
    {hf : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker f} (hfv : f v = 1)
    {hg : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker (f + g)} (hfgv : (f + g) v = 1)
    (hg0 : g ≠ 0) (hne_top : e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v < ⊤)
    (ha : ∀ x, (auxTransvection hf * e).fixedReduce x = a • x)
    (hb : ∀ x, (auxTransvection hg * e).fixedReduce x = b • x) :
    False := by
  have key1 : ∀ y, (auxTransvection hf * e) y - a • y ∈ e.fixedSubmodule ⊔ K ∙ v := by
    intro y
    have h1 := ha (Submodule.Quotient.mk y)
    first
      | rw [fixedReduce_mk] at h1
      | simp only [fixedReduce_mk] at h1
      | rw [← Submodule.mkQ_apply, fixedReduce_mk, Submodule.mkQ_apply] at h1
    have h2 : a • (Submodule.Quotient.mk y : V ⧸ (auxTransvection hf * e).fixedSubmodule) =
        Submodule.Quotient.mk (a • y) := by
      first
        | rfl
        | exact (Submodule.Quotient.mk_smul _ a y).symm
        | simp
    have h3 := h1.trans h2
    rw [Submodule.Quotient.eq, auxTransvection_mul_fixed hfv] at h3
    exact h3
  have key2 : ∀ y, (auxTransvection hg * e) y - b • y ∈ e.fixedSubmodule ⊔ K ∙ v := by
    intro y
    have h1 := hb (Submodule.Quotient.mk y)
    first
      | rw [fixedReduce_mk] at h1
      | simp only [fixedReduce_mk] at h1
      | rw [← Submodule.mkQ_apply, fixedReduce_mk, Submodule.mkQ_apply] at h1
    have h2 : b • (Submodule.Quotient.mk y : V ⧸ (auxTransvection hg * e).fixedSubmodule) =
        Submodule.Quotient.mk (b • y) := by
      first
        | rfl
        | exact (Submodule.Quotient.mk_smul _ b y).symm
        | simp
    have h3 := h1.trans h2
    rw [Submodule.Quotient.eq, auxTransvection_mul_fixed hfgv] at h3
    exact h3
  have hu1 : ∀ y, (auxTransvection hf * e) y = e y + f (e y) • (v - e v) := by
    intro y
    first
      | rfl
      | (simp only [auxTransvection, LinearEquiv.mul_apply, transvection.apply]; done)
      | simp [auxTransvection, LinearMap.transvection.apply]
  have hu2 : ∀ y, (auxTransvection hg * e) y = e y + (f + g) (e y) • (v - e v) := by
    intro y
    first
      | rfl
      | (simp only [auxTransvection, LinearEquiv.mul_apply, transvection.apply]; done)
      | simp [auxTransvection, LinearMap.transvection.apply]
  have key : ∀ y, g (e y) • (v - e v) + (a - b) • y ∈ e.fixedSubmodule ⊔ K ∙ v := by
    intro y
    have h3 := sub_mem (key2 y) (key1 y)
    rw [hu1, hu2] at h3
    convert h3 using 1
    first
      | (simp only [LinearMap.add_apply, add_smul, sub_smul]; abel)
      | (simp only [LinearMap.add_apply, add_smul, sub_smul, smul_sub]; abel)
      | (simp only [Module.Dual, LinearMap.add_apply, add_smul, sub_smul]; abel)
  by_cases hab : a = b
  · subst hab
    obtain ⟨w, hw⟩ : ∃ w, g w ≠ 0 := by
      by_contra! h
      apply hg0
      ext w
      simpa using h w
    have hk := key (e.symm w)
    rw [e.apply_symm_apply, sub_self, zero_smul, add_zero] at hk
    have hk' : v - e v ∈ e.fixedSubmodule ⊔ K ∙ v := by
      have h4 := Submodule.smul_mem _ (g w)⁻¹ hk
      rwa [smul_smul, inv_mul_cancel₀ hw, one_smul] at h4
    have hev : e v ∈ e.fixedSubmodule ⊔ K ∙ v := by
      have h4 := sub_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)) hk'
      rwa [sub_sub_cancel] at h4
    obtain ⟨w₀, hw₀, z, hz, hwz⟩ := Submodule.mem_sup.mp hev
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hq : (Submodule.Quotient.mk (e v) : V ⧸ e.fixedSubmodule) =
        c • Submodule.Quotient.mk v := by
      rw [← hwz, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).mpr hw₀, zero_add]
      all_goals
        first
          | rfl
          | exact Submodule.Quotient.mk_smul _ c v
          | simp
    have hsum : c • e.fixedSubmodule.mkQ v +
        (-1 : K) • e.fixedReduce (e.fixedSubmodule.mkQ v) = 0 := by
      first
        | (rw [Submodule.mkQ_apply, fixedReduce_mk, hq, neg_smul, one_smul]
           exact add_neg_cancel _)
        | simp [fixedReduce_mk, hq]
    have h0 := LinearIndependent.pair_iff.mp hv c (-1) hsum
    exact one_ne_zero (neg_eq_zero.mp h0.2)
  · apply hne_top.ne
    rw [Submodule.eq_top_iff']
    intro y
    have hW : e.fixedSubmodule ⊔ K ∙ v ≤ e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v :=
      sup_le_sup_right le_sup_left _
    have hvev : v - e v ∈ e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v := by
      apply Submodule.mem_sup_left
      apply Submodule.mem_sup_right
      rw [Submodule.mem_span_singleton]
      exact ⟨-1, by simp⟩
    have h4 := sub_mem (hW (key y)) (Submodule.smul_mem _ (g (e y)) hvev)
    have e1 : g (e y) • (v - e v) + (a - b) • y - g (e y) • (v - e v) = (a - b) • y := by
      abel
    rw [e1] at h4
    have h5 := Submodule.smul_mem _ (a - b)⁻¹ h4
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] at h5
