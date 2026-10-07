/-
Machine-generated proof, verified by Lean.

Theorem:      PiTensorProduct.ext_of_span_eq_top
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean, line 129
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  32 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) →ₗ[R] N}
    (h : ∀ (j : (i : ι) → γ i),
      φ (tprod _ (fun i ↦ g (j i))) = φ' (tprod _ (fun i ↦ g (j i)))) :
    φ = φ' := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ f f' : MultilinearMap R M N,
      (∀ j : (i : ι) → γ i, f (fun i ↦ g (j i)) = f' (fun i ↦ g (j i))) → f = f' by
    exact PiTensorProduct.ext
      (H (φ.compMultilinearMap (tprod R)) (φ'.compMultilinearMap (tprod R)) h)
  intro f f' h'
  have key : ∀ (S : Finset ι) (m : (i : ι) → M i), (∀ i ∉ S, m i ∈ Set.range (@g i)) →
      f m = f' m := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro m hm
      choose j hj using fun i ↦ Set.mem_range.mp (hm i (by simp))
      have hm' : m = fun i ↦ g (j i) := funext fun i ↦ (hj i).symm
      rw [hm']
      exact h' j
    | @insert a S ha ih =>
      intro m hm
      have hlin : f.toLinearMap m a = f'.toLinearMap m a := by
        refine LinearMap.ext_on_range (hg a) (fun k ↦ ?_)
        show f (Function.update m a (g k)) = f' (Function.update m a (g k))
        apply ih
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · first
            | rw [Function.update_of_ne hia]
            | rw [Function.update_noteq hia]
          exact hm i (by simp [hia, hi])
      have h2 := LinearMap.congr_fun hlin (m a)
      change f (Function.update m a (m a)) = f' (Function.update m a (m a)) at h2
      first
        | (rwa [Function.update_eq_self] at h2)
        | simpa using h2
  exact MultilinearMap.ext fun m ↦ key Finset.univ m (by simp)
