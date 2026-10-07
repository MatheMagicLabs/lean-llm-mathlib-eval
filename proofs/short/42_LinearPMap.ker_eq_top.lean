/-
Machine-generated proof, verified by Lean.

Theorem:      LinearPMap.ker_eq_top
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/LinearPMap.lean, line 407
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem ker_eq_top {f : E →ₛₗ.[σ] F} : f.ker = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    have hdom : f.domain = ⊤ := by
      rw [eq_top_iff, ← h]
      exact ker_le_domain
    refine LinearPMap.ext ?_ ?_
    · exact hdom
    · intro x hx hx'
      have hfx : f ⟨x, hx⟩ = 0 := coe_mem_ker_iff.mp (by rw [h]; exact Submodule.mem_top)
      exact hfx.trans rfl
  · rintro rfl
    exact ker_zero
