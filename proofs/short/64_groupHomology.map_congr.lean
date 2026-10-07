/-
Machine-generated proof, verified by Lean.

Theorem:      groupHomology.map_congr
Source:       Mathlib @ d0a050ad6, Mathlib/RepresentationTheory/Homological/GroupHomology/Functoriality.lean, line 161
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: RepresentationTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma map_congr {f g : G →* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℕ) :
    map f φ n = map g ψ n := by
  exact congrArg (fun x => HomologicalComplex.homologyMap x n) (chainsMap_congr hfg hφψ)
