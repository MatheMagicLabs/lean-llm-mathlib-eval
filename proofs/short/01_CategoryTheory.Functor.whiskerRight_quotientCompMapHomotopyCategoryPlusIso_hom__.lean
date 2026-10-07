/-
Machine-generated proof, verified by Lean.

Theorem:      CategoryTheory.Functor.whiskerRight_quotientCompMapHomotopyCategoryPlusIso_hom_ι
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean, line 348
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  5 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma whiskerRight_quotientCompMapHomotopyCategoryPlusIso_hom_ι :
    whiskerRight F.quotientCompMapHomotopyCategoryPlusIso.hom (HomotopyCategory.Plus.ι D) =
    (associator _ _ _).hom ≫
      whiskerLeft _ F.mapHomotopyCategoryPlusCompι.hom ≫ (associator _ _ _).inv ≫
      whiskerRight (HomotopyCategory.Plus.quotientCompιIso C).hom _ ≫
      (associator _ _ _).hom ≫ whiskerLeft _ (F.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
      (associator _ _ _).inv ≫ whiskerRight F.mapCochainComplexPlusCompι.inv _ ≫
      (associator _ _ _).hom ≫ whiskerLeft _ (HomotopyCategory.Plus.quotientCompιIso D).inv ≫
      (associator _ _ _).inv := by
  ext K
  dsimp [quotientCompMapHomotopyCategoryPlusIso, mapHomotopyCategoryPlusCompι,
    HomotopyCategory.Plus.quotientCompιIso, ObjectProperty.liftCompιIso,
    mapCochainComplexPlusCompι, mapHomotopyCategoryFactors]
  simp
  first
  | (erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp]; done)
  | (erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp]; rfl)
  | (erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.comp_id]; done)
  | (erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.comp_id]; rfl)
  | (set_option backward.isDefEq.respectTransparency false in simp)
