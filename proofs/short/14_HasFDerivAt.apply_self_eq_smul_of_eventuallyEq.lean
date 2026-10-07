/-
Machine-generated proof, verified by Lean.

Theorem:      HasFDerivAt.apply_self_eq_smul_of_eventuallyEq
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Calculus/LineDeriv/Basic.lean, line 284
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem HasFDerivAt.apply_self_eq_smul_of_eventuallyEq {w : 𝕜 → 𝕜} {w' : 𝕜}
    (hf : HasFDerivAt f L x) (hw : HasDerivAt w w' 1)
    (hhom : (fun t ↦ f (t • x)) =ᶠ[𝓝 1] fun t ↦ w t • f x) : L x = w' • f x := by
  let g : 𝕜 → E := fun t => t • x
  have hg : HasDerivAt g x 1 := by
    have h := (hasDerivAt_id (1 : 𝕜)).smul_const x
    rw [one_smul] at h
    exact h
  have hf' : HasFDerivAt f L (g 1) := by
    show HasFDerivAt f L ((1 : 𝕜) • x)
    rw [one_smul]
    exact hf
  have h1 : HasDerivAt (f ∘ g) (L x) 1 := hf'.comp_hasDerivAt (x := (1 : 𝕜)) hg
  have h2 : HasDerivAt (fun t : 𝕜 => f (t • x)) (w' • f x) 1 :=
    (hw.smul_const (f x)).congr_of_eventuallyEq hhom
  exact h1.unique h2
