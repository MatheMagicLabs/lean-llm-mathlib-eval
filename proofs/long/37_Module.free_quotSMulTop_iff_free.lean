/-
Machine-generated proof, verified by Lean.

Theorem:      Module.free_quotSMulTop_iff_free
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/Regular/Free.lean, line 34
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  29 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma Module.free_quotSMulTop_iff_free [Module.FinitePresentation R M] {x : R}
    (mem : x ∈ (⊥ : Ideal R).jacobson) (reg : IsSMulRegular M x) :
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M := by
  refine ⟨fun free ↦ ?_, fun _ ↦ inferInstance⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := Module.subsingleton R M
    first
      | infer_instance
      | exact Module.Free.of_subsingleton' R M
      | exact Module.Free.of_subsingleton R M
  have lejac : Ideal.span {x} ≤ (⊥ : Ideal R).jacobson :=
    (Ideal.span_singleton_le_iff_mem _).2 mem
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro htop
    rw [htop, top_le_iff, Ideal.jacobson_eq_top_iff, Ideal.eq_top_iff_one, Ideal.mem_bot] at lejac
    exact one_ne_zero lejac
  haveI : Nontrivial (R ⧸ Ideal.span {x}) := by
    first
      | exact Ideal.Quotient.nontrivial hne
      | exact Ideal.Quotient.nontrivial_iff.2 hne
  haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  haveI : _root_.Finite
      (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) := by
    first
      | exact Module.Finite.finite_basis b
      | infer_instance
  haveI : Module.Free R
      (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M) → R) :=
    Module.Free.of_basis (Pi.basisFun R _)
  haveI : Module.Finite R
      (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M) → R) := by
    first
      | infer_instance
      | exact Module.Finite.of_basis (Pi.basisFun R _)
  obtain ⟨f, hf⟩ : ∃ f : (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M) →
      R) →ₗ[R] QuotSMulTop x M,
      ∀ v, f v = b.equivFun.symm (fun i ↦ algebraMap R (R ⧸ Ideal.span {x}) (v i)) := by
    first
      | exact ⟨(b.equivFun.symm.restrictScalars R).toLinearMap ∘ₗ
          LinearMap.pi (fun i ↦ (Algebra.linearMap R (R ⧸ Ideal.span {x})) ∘ₗ LinearMap.proj i),
          fun v ↦ rfl⟩
      | exact ⟨(b.equivFun.symm.restrictScalars R).toLinearMap ∘ₗ
          LinearMap.compLeft (Algebra.linearMap R (R ⧸ Ideal.span {x})) _, fun v ↦ rfl⟩
      | exact ⟨(b.equivFun.symm.restrictScalars R).toLinearMap ∘ₗ
          LinearMap.pi (fun i ↦ (Algebra.linearMap R (R ⧸ Ideal.span {x})) ∘ₗ LinearMap.proj i),
          fun v ↦ by simp⟩
  have surjf : Function.Surjective f := by
    intro n
    choose d hd using fun i ↦ Ideal.Quotient.mk_surjective (b.equivFun n i)
    refine ⟨d, ?_⟩
    rw [hf, ← b.equivFun.symm_apply_apply n]
    congr 1
    funext i
    rw [Ideal.Quotient.algebraMap_eq]
    exact hd i
  have kerf : ∀ v, f v = 0 → ∀ i, v i ∈ Ideal.span {x} := by
    intro v hv i
    rw [hf, LinearEquiv.map_eq_zero_iff] at hv
    have h2 : algebraMap R (R ⧸ Ideal.span {x}) (v i) = 0 := congrFun hv i
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h2
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (x • (⊤ : Submodule R M)).mkQ f
    (Submodule.mkQ_surjective _)
  have surjg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.1 inferInstance)
      lejac ?_
    rw [Submodule.ideal_span_singleton_smul]
    intro m _
    obtain ⟨v, hv⟩ := surjf (Submodule.Quotient.mk m)
    have h1 : (Submodule.Quotient.mk m : QuotSMulTop x M) = Submodule.Quotient.mk (g v) :=
      hv.symm.trans (LinearMap.congr_fun hg v).symm
    rw [Submodule.Quotient.eq] at h1
    rw [Submodule.mem_sup]
    exact ⟨g v, LinearMap.mem_range_self g v, m - g v, h1, by abel⟩
  have hker : LinearMap.ker g = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _
      (Module.FinitePresentation.fg_ker g surjg) ?_ lejac
    rw [Submodule.ideal_span_singleton_smul]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have hfv : f v = 0 := by
      rw [← LinearMap.congr_fun hg v, LinearMap.comp_apply, hv, map_zero]
    have hvi := kerf v hfv
    choose d hd using fun i ↦ Ideal.mem_span_singleton'.1 (hvi i)
    have hxd : x • d = v := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hd i]
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨d, ?_, hxd⟩
    rw [LinearMap.mem_ker]
    have h3 : x • g d = x • (0 : M) := by
      rw [← map_smul, hxd, hv, smul_zero]
    exact reg h3
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨LinearMap.ker_eq_bot.1 hker, surjg⟩)
