/-
Machine-generated proof, verified by Lean.

Theorem:      intrinsicInterior_image_of_homeomorph_affineSpan
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Convex/Intrinsic.lean, line 255
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private theorem intrinsicInterior_image_of_homeomorph_affineSpan :
    intrinsicInterior 𝕜 (f '' s) = f '' intrinsicInterior 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  haveI : Nonempty s := hne.to_subtype
  have key := preimage_image_eq_of_homeomorph_affineSpan e he_homeo he
  have hcomp : Subtype.val ∘ e = f ∘ Subtype.val := funext he
  have hpre : e ⁻¹' (Subtype.val ⁻¹' (f '' s) : Set (affineSpan 𝕜 (f '' s))) =
      (Subtype.val ⁻¹' s : Set (affineSpan 𝕜 s)) := by
    rw [← Set.preimage_comp, hcomp, key]
  have hint : interior (Subtype.val ⁻¹' (f '' s) : Set (affineSpan 𝕜 (f '' s))) =
      e '' interior (Subtype.val ⁻¹' s : Set (affineSpan 𝕜 s)) := by
    rw [← hpre, ← he_homeo.isOpenMap.preimage_interior_eq_interior_preimage he_homeo.continuous,
      Set.image_preimage_eq _ he_homeo.bijective.surjective]
  simp only [intrinsicInterior]
  rw [hint, Set.image_image, Set.image_image]
  simp only [he]
