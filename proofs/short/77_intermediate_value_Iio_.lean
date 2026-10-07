/-
Machine-generated proof, verified by Lean.

Theorem:      intermediate_value_Iio'
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/Order/IntermediateValue.lean, line 726
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem intermediate_value_Iio' {a : α} {f : α → δ} (hf : ContinuousOn f (Iic a))
    (hbot : Tendsto f atBot atTop) : Ioi (f a) ⊆ f '' Iio a := by
  intro y hy
  have := intermediate_value_Iic' hf hbot (mem_Ici_of_Ioi hy)
  first
    | grind
    | (obtain ⟨x, hx, rfl⟩ := this; exact ⟨x, lt_of_le_of_ne hx (by rintro rfl; exact lt_irrefl _ hy), rfl⟩)
