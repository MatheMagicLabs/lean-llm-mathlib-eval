/-
Machine-generated proof, verified by Lean.

Theorem:      ModuleCat.subsingleton_ext_of_exists_isRegular
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/Depth/Rees.lean, line 101
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  25 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma subsingleton_ext_of_exists_isRegular [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < rs.length, Subsingleton (Ext N M i) := by
  induction rs generalizing M with
  | nil =>
    intro i hi
    simp at hi
  | cons x rs' ih =>
    intro i hi
    rw [isRegular_cons_iff] at reg
    obtain ⟨hx, reg'⟩ := reg
    have hxI : x ∈ I := mem x (by simp)
    have mem' : ∀ r ∈ rs', r ∈ I := fun r hr ↦ mem r (by simp [hr])
    have hsupp := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsupp
    obtain ⟨k, hk⟩ := hsupp hxI
    rcases i with _ | i
    · have h1 : Subsingleton (N →ₗ[R] M) :=
        subsingleton_linearMap_iff.mpr ⟨x ^ k, hk, hx.pow k⟩
      have h2 : Subsingleton (N ⟶ M) := ModuleCat.homAddEquiv.subsingleton
      exact Ext.addEquiv₀.subsingleton
    · have hi' : i < rs'.length := by simpa using hi
      have hsub : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) :=
        ih (ModuleCat.of R (QuotSMulTop x M))
          (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hxI smul_lt.ne).lt_top mem' reg' i hi'
      have hS := hx.smulShortComplex_shortExact
      have hf : (ModuleCat.smulShortComplex M x).f = x • 𝟙 M := by
        first
          | rfl
          | (ext m; simp [ModuleCat.smulShortComplex]; done)
          | (ext m; simp; done)
          | (ext m; rfl)
      have inj : ∀ e : Ext N M (i + 1), x • e = 0 → e = 0 := by
        intro e he
        have h1 : e.comp (Ext.mk₀ (x • 𝟙 M)) (add_zero (i + 1)) = x • e := by
          first
            | rw [Ext.mk₀_smul, Ext.comp_smul, Ext.comp_mk₀_id]
            | (simp; done)
            | (simp [Ext.mk₀_smul, Ext.comp_smul]; done)
            | exact (Ext.smul_eq_comp_mk₀ _ _).symm
        have he' : e.comp (Ext.mk₀ (ModuleCat.smulShortComplex M x).f) (add_zero (i + 1)) = 0 :=
          (congrArg (fun f ↦ e.comp (Ext.mk₀ f) (add_zero (i + 1))) hf).trans (h1.trans he)
        first
          | (obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ N hS e he' (n₀ := i) rfl
             have hy0 : y = 0 := @Subsingleton.elim _ (by exact hsub) y 0
             rw [hy0] at hy
             first
               | (simp only [Ext.zero_comp] at hy; first | exact hy | exact hy.symm)
               | (simp at hy; first | exact hy | exact hy.symm))
          | (obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ N hS e he' rfl
             have hy0 : y = 0 := @Subsingleton.elim _ (by exact hsub) y 0
             rw [hy0] at hy
             first
               | (simp only [Ext.zero_comp] at hy; first | exact hy | exact hy.symm)
               | (simp at hy; first | exact hy | exact hy.symm))
          | (obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
               (Ext.covariant_sequence_exact₁' N hS i (i + 1) rfl) e he'
             have hy0 : y = 0 := @Subsingleton.elim _ (by exact hsub) y 0
             rw [hy0] at hy
             simp at hy
             first | exact hy | exact hy.symm)
      have h0 : x ^ k • 𝟙 N = 0 := by
        ext n
        first
          | (simp [Module.mem_annihilator.mp hk n]; done)
          | exact Module.mem_annihilator.mp hk n
      have kill : ∀ e : Ext N M (i + 1), x ^ k • e = 0 := by
        intro e
        first
          | rw [← Ext.mk₀_id_comp e, ← Ext.smul_comp, ← Ext.mk₀_smul, h0, Ext.mk₀_zero,
              Ext.zero_comp]
          | (have := congrArg (fun f ↦ (Ext.mk₀ f).comp e (zero_add (i + 1))) h0
             simpa using this)
      have key : ∀ j : ℕ, ∀ e : Ext N M (i + 1), x ^ j • e = 0 → e = 0 := by
        intro j
        induction j with
        | zero =>
          intro e he
          simpa using he
        | succ j ihj =>
          intro e he
          apply inj
          apply ihj
          rw [← mul_smul, ← pow_succ]
          exact he
      exact ⟨fun a b ↦ by rw [key k a (kill a), key k b (kill b)]⟩
