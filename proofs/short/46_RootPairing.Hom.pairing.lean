/-
Machine-generated proof, verified by Lean.

Theorem:      RootPairing.Hom.pairing
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/RootSystem/Hom.lean, line 80
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

@[simp] lemma pairing {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} (f : Hom P Q) {i j : ι} :
    Q.pairing (f.indexEquiv i) (f.indexEquiv j) = P.pairing i j := by
  have h1 : f.weightMap (P.root i) = Q.root (f.indexEquiv i) := congr_fun f.root_weightMap i
  have h2 : f.coweightMap (Q.coroot (f.indexEquiv j)) = P.coroot j := by
    have h := congr_fun f.coroot_coweightMap (f.indexEquiv j)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at h
    exact h
  have h3 := LinearMap.congr_fun
    (LinearMap.congr_fun f.weight_coweight_transpose (Q.coroot (f.indexEquiv j))) (P.root i)
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe, h1, h2] at h3
  first
    | simpa using h3
    | exact h3
    | exact h3.symm
