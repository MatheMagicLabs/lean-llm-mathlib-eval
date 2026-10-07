/-
Machine-generated proof, verified by Lean.

Theorem:      affineSpan_image_ne_top_of_encard_le_finrank
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean, line 236
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  10 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma affineSpan_image_ne_top_of_encard_le_finrank {s : Set ι} (hsfin : s.Finite)
    (hs : s.encard ≤ finrank k V) (p : ι → P) : affineSpan k (p '' s) ≠ ⊤ := by
  classical
  intro h
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [Set.image_empty] at h
    first
      | exact AffineSubspace.bot_ne_top k V P (by rwa [AffineSubspace.span_empty] at h)
      | exact AffineSubspace.bot_ne_top (by rwa [AffineSubspace.span_empty] at h)
      | exact bot_ne_top (by rwa [AffineSubspace.span_empty] at h)
      | (simp at h; done)
      | (obtain ⟨q⟩ := (inferInstance : Nonempty P); have hq : q ∈ affineSpan k (∅ : Set P) := (by rw [h]; exact AffineSubspace.mem_top k V q); simp at hq)
  · obtain ⟨t, rfl⟩ := hsfin.exists_finset_coe
    have hcard : t.card ≤ finrank k V := by
      first
        | (rw [Set.encard_coe_eq_coe_finsetCard] at hs; exact_mod_cast hs)
        | (simp at hs; exact_mod_cast hs)
    have hpos : 0 < t.card := Finset.card_pos.mpr (by simpa using hne)
    have hle := finrank_vectorSpan_image_finset_le k p t (n := t.card - 1) (by omega)
    have htop : vectorSpan k (p '' (t : Set ι)) = ⊤ := by
      first
        | rw [← direction_affineSpan, h, AffineSubspace.direction_top]
        | simp [← direction_affineSpan, h]
    rw [Finset.coe_image, htop] at hle
    first
      | (rw [finrank_top] at hle; omega)
      | (simp only [finrank_top] at hle; omega)
      | (simp at hle; omega)
