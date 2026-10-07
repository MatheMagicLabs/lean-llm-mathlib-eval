/-
Machine-generated proof, verified by Lean.

Theorem:      NormedSpace.log_op
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Normed/Algebra/Logarithm.lean, line 150
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem log_op [T2Space 𝔸] (x : 𝔸) : log (MulOpposite.op x) = MulOpposite.op (log x) := by
  by_cases h : Nonempty (Algebra ℚ 𝔸)
  · obtain ⟨inst⟩ := h
    first
      | simp_rw [log_eq_tsum (𝔸 := 𝔸ᵐᵒᵖ) ℚ, log_eq_tsum (𝔸 := 𝔸) ℚ]
      | simp_rw [log_eq_tsum ℚ]
    simp_rw [← MulOpposite.op_one, ← MulOpposite.op_sub, ← MulOpposite.op_pow,
      ← MulOpposite.op_smul, tsum_op]
  · have key : Algebra ℚ 𝔸ᵐᵒᵖ → Algebra ℚ 𝔸 := fun inst ↦
      RingHom.toAlgebra'
        ({ toFun := fun q ↦ MulOpposite.unop (algebraMap ℚ 𝔸ᵐᵒᵖ q)
           map_one' := by simp
           map_mul' := fun a b ↦ by simp only [mul_comm a b, map_mul, MulOpposite.unop_mul]
           map_zero' := by simp
           map_add' := fun a b ↦ by simp } : ℚ →+* 𝔸)
        fun c x ↦ (congrArg MulOpposite.unop (Algebra.commutes c (MulOpposite.op x))).symm
    haveI : IsEmpty (Algebra ℚ 𝔸) := not_nonempty_iff.mp h
    haveI : IsEmpty (Algebra ℚ 𝔸ᵐᵒᵖ) := ⟨fun inst ↦ h ⟨key inst⟩⟩
    first
      | simp
      | rw [log_of_isEmpty_algebra_rat, log_of_isEmpty_algebra_rat, MulOpposite.op_zero]
