/-
Machine-generated proof, verified by Lean.

Theorem:      Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/Kaehler/JacobiZariski.lean, line 496
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  13 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exact_liftBaseChange_map_of_flat [Module.Flat S T] :
    Function.Exact ((Extension.H1Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
      (Extension.H1Cotangent.map (ofComp Q P).toExtensionHom) := by
  have key : ∀ u : T ⊗[S] P.toExtension.H1Cotangent,
      (Q.comp P).toExtension.h1Cotangentι
          ((Extension.H1Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T u) =
        (Extension.Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T
          (P.toExtension.h1Cotangentι.lTensor T u) := by
    intro u
    induction u with
    | tmul a b =>
      simp only [LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, map_smul]
      try rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [LinearMap.exact_iff]
  refine le_antisymm ?_ (liftBaseChange_range_le Q P)
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [LinearMap.mem_range]
  have h1 : Extension.Cotangent.map (ofComp Q P).toExtensionHom x.1 = 0 := by
    have := congrArg Subtype.val hx
    exact this
  obtain ⟨z, hz⟩ := (Cotangent.exact Q P x.1).mp h1
  have h2 : (Q.comp P).toExtension.cotangentComplex x.1 = 0 := LinearMap.mem_ker.mp x.2
  have h3 : P.toExtension.cotangentComplex.baseChange T z = 0 := by
    apply CotangentSpace.map_toComp_injective Q P
    rw [map_zero]
    have := LinearMap.congr_fun (map_comp_cotangentComplex_baseChange Q P) z
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.comp_apply] at this
    rw [this, hz, h2]
  have h3' : P.toExtension.cotangentComplex.lTensor T z = 0 := by
    first
      | (rw [← LinearMap.baseChange_eq_ltensor]; exact h3)
      | exact h3
  have hex : Function.Exact P.toExtension.h1Cotangentι P.toExtension.cotangentComplex :=
    LinearMap.exact_subtype_ker_map _
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact (R := S) (M := T) hex z).mp h3'
  refine ⟨w, Subtype.ext ?_⟩
  rw [← hz, ← hw]
  exact key w
