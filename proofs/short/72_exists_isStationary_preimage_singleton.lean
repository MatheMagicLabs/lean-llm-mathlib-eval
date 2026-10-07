/-
Machine-generated proof, verified by Lean.

Theorem:      exists_isStationary_preimage_singleton
Source:       Mathlib @ d0a050ad6, Mathlib/SetTheory/Cardinal/Cofinality/Club.lean, line 338
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  7 tactic steps; area: SetTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_isStationary_preimage_singleton [IsRegularCardinalOrder α] {f : α → α}
    (hα : cof α ≠ ℵ₀) (hs : IsStationary s) (hf : ∀ x ∈ s, f x < x) :
    ∃ a, IsStationary (s ∩ f ⁻¹' {a}) := by
  by_contra hcon
  have h' : ∀ a, ∃ t, IsClub t ∧ Disjoint (s ∩ f ⁻¹' {a}) t := fun a =>
    not_isStationary_iff.1 fun ha => hcon ⟨a, ha⟩
  choose C hC hdisj using h'
  obtain ⟨x, hxs, hxD⟩ := hs (IsClub.diag hα hC)
  have hxD' : ∀ b < x, x ∈ C b := hxD
  have hx1 : x ∈ C (f x) := hxD' (f x) (hf x hxs)
  have hmem : x ∈ s ∩ f ⁻¹' {f x} := ⟨hxs, rfl⟩
  exact Set.disjoint_left.1 (hdisj (f x)) hmem hx1
