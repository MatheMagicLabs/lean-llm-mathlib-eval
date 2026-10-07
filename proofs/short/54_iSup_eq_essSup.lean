/-
Machine-generated proof, verified by Lean.

Theorem:      iSup_eq_essSup
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/EssSup.lean, line 323
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  6 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma iSup_eq_essSup {f : α → β} (h : ∀ ⦃x a⦄, a < f x → μ {y | a < f y} ≠ 0) :
    ⨆ x, f x = essSup f μ := by
  refine le_antisymm ?_ essSup_le_iSup
  refine le_trans ?_ (essSup_eq_sInf μ f).ge
  refine iSup_le fun x => le_sInf fun a ha => ?_
  by_contra hlt
  exact h (not_le.mp hlt) ha
