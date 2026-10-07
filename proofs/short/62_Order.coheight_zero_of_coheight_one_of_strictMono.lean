/-
Machine-generated proof, verified by Lean.

Theorem:      Order.coheight_zero_of_coheight_one_of_strictMono
Source:       Mathlib @ d0a050ad6, Mathlib/Order/KrullDimension.lean, line 1060
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Order
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma coheight_zero_of_coheight_one_of_strictMono
    {α β : Type*} [Preorder α] [Preorder β] (f : WithTop α → β) (hf : StrictMono f) (x : α)
    (h : coheight (f x) = 1) : coheight x = 0 := by
  have h1 := coheight_le_coheight_apply_of_strictMono f hf (x : WithTop α)
  rw [h, coheight_coe_withTop] at h1
  cases hc : coheight x with
  | top =>
    rw [hc] at h1
    first
      | exact absurd (top_le_iff.mp (le_self_add.trans h1)) ENat.one_ne_top
      | simp at h1
  | coe n =>
    rw [hc] at h1
    have h2 : n + 1 ≤ 1 := by exact_mod_cast h1
    have hn : n = 0 := by omega
    simp [hn]
