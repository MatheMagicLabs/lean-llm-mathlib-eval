/-
Machine-generated proof, verified by Lean.

Theorem:      lowerHemicontinuous_singleton_id
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/Semicontinuity/Hemicontinuity.lean, line 203
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma lowerHemicontinuous_singleton_id : LowerHemicontinuous ({·} : α → Set α) := by
  first
  | (rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
     intro u hu
     simpa [Set.singleton_inter_nonempty] using hu)
  | (rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
     intro u hu
     convert hu using 1
     ext y
     simp [Set.Nonempty])
  | (simpa using isOpenMap_iff_lowerHemicontinuous.mp (IsOpenMap.id : IsOpenMap (id : α → α)))
