/-
Machine-generated proof, verified by Lean.

Theorem:      Manifold.IsSubmersionOfComplement.isSubmersion
Source:       Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/Submersion.lean, line 588
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  6 tactic steps; area: Geometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n f := by
  by_cases hM : Nonempty M
  · obtain ⟨x⟩ := hM
    first
      | exact ⟨(h x).smallComplement, inferInstance, inferInstance, (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h⟩
      | (use (h x).smallComplement, inferInstance, inferInstance; exact (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h)
  · first
      | exact ⟨PUnit, inferInstance, inferInstance, fun y => (hM ⟨y⟩).elim⟩
      | exact ⟨E, inferInstance, inferInstance, fun y => (hM ⟨y⟩).elim⟩
      | exact ⟨E'', inferInstance, inferInstance, fun y => (hM ⟨y⟩).elim⟩
      | exact ⟨E', inferInstance, inferInstance, fun y => (hM ⟨y⟩).elim⟩
      | exact ⟨E''', inferInstance, inferInstance, fun y => (hM ⟨y⟩).elim⟩
      | exact ⟨Shrink.{u} (Fin 0 → 𝕜), inferInstance, inferInstance, fun y => (hM ⟨y⟩).elim⟩
