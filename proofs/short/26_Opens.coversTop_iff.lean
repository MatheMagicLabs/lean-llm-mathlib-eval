/-
Machine-generated proof, verified by Lean.

Theorem:      Opens.coversTop_iff
Source:       Mathlib @ d0a050ad6, Mathlib/CategoryTheory/Sites/Spaces.lean, line 99
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  8 tactic steps; area: CategoryTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma coversTop_iff {ι : Type*} (U : ι → Opens T) :
    (grothendieckTopology T).CoversTop U ↔ IsOpenCover U := by
  constructor
  · intro h
    have key : ∀ x : T, ∃ i, x ∈ U i := by
      intro x
      obtain ⟨V, g, ⟨i, ⟨g'⟩⟩, hx⟩ := h ⊤ x (by first | trivial | simp)
      exact ⟨i, g'.le hx⟩
    first
      | exact isOpenCover_iff.mpr key
      | exact IsOpenCover.mk key
      | exact IsOpenCover.mk (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr (key x))
      | (show iSup U = ⊤; exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr (key x))
  · intro h X x hx
    have hx' : ∃ i, x ∈ U i := by
      first
        | exact isOpenCover_iff.mp h x
        | exact h.exists_mem x
        | exact Opens.mem_iSup.mp (by rw [show iSup U = ⊤ from h]; trivial)
    obtain ⟨i, hi⟩ := hx'
    exact ⟨X ⊓ U i, homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩, hx, hi⟩
