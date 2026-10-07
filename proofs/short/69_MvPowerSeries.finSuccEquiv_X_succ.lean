/-
Machine-generated proof, verified by Lean.

Theorem:      MvPowerSeries.finSuccEquiv_X_succ
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPowerSeries/Equiv.lean, line 191
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  7 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.9 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem finSuccEquiv_X_succ (j : Fin n) : finSuccEquiv R n (X j.succ) = .C (X j) := by
  first
  | (ext k x
     rw [coeff_coeff_finSuccEquiv, coeff_X, PowerSeries.coeff_C]
     by_cases hk : k = 0
     · subst hk
       rw [if_pos (rfl : (0 : ℕ) = 0), coeff_X]
       by_cases hx : x = Finsupp.single j 1
       · rw [if_pos hx, if_pos]
         subst hx
         ext i
         refine Fin.cases ?_ (fun i ↦ ?_) i
         · simp [Fin.succ_ne_zero, Finsupp.single_apply]
         · simp [Finsupp.single_apply]
       · rw [if_neg hx, if_neg]
         intro h
         apply hx
         ext i
         simpa [Finsupp.single_apply] using DFunLike.congr_fun h i.succ
     · rw [if_neg hk, coeff_zero, if_neg]
       intro h
       apply hk
       simpa [Fin.succ_ne_zero, Finsupp.single_apply] using DFunLike.congr_fun h 0)
  | (simp [finSuccEquiv]; done)
  | (simp [finSuccEquiv, rename_X]; done)
