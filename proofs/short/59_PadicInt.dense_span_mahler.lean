/-
Machine-generated proof, verified by Lean.

Theorem:      PadicInt.dense_span_mahler
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/Padics/MahlerBasis.lean, line 398
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  8 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem dense_span_mahler : Dense (span R
      (.range fun n ↦ (mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) : Set C(ℤ_[p], R)) := by
  intro f
  have key : ∀ (a : R) (n : ℕ), (mahlerTerm a n : C(ℤ_[p], R)) =
      a • ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) := by
    intro a n
    ext x
    first
    | (rw [mahlerTerm_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply',
         ContinuousMap.one_apply, smul_eq_mul, mul_smul_comm, mul_one]; done)
    | (simp [mahlerTerm_apply, Algebra.smul_def, mul_comm]; done)
    | (simp [mahlerTerm_apply, mul_smul_comm]; done)
    | (simp only [mahlerTerm_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply',
         ContinuousMap.one_apply, smul_eq_mul, Algebra.smul_def, mul_one, mul_comm])
  refine mem_closure_of_tendsto (hasSum_mahler f).tendsto_sum_nat
    (Filter.Eventually.of_forall fun n ↦ ?_)
  refine SetLike.mem_coe.mpr (_root_.sum_mem fun i _ ↦ ?_)
  first
  | (rw [key]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  | (simp only [key]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
