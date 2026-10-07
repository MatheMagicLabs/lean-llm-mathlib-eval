/-
Machine-generated proof, verified by Lean.

Theorem:      Ideal.IsFractionRing.normal
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/Invariant/Galois.lean, line 84
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  32 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma normal : Normal K L := by
  classical
  cases nonempty_fintype G
  haveI : Nontrivial B :=
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk Q)).nontrivial
  have hlift : ∀ b : B, ∃ f : Polynomial A,
      f.map (algebraMap A B) = ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) ∧ f.Monic := by
    intro b
    have hmonic : (∏ g : G, (Polynomial.X - Polynomial.C (g • b))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _
    have hmem : (∏ g : G, (Polynomial.X - Polynomial.C (g • b))) ∈
        Polynomial.lifts (algebraMap A B) := by
      first
        | exact Algebra.IsInvariant.charpoly_mem_lifts A B G b
        | exact Algebra.IsInvariant.charpoly_mem_lifts (A := A) (B := B) (G := G) b
        | (rw [Polynomial.lifts_iff_coeff_lifts]
           intro n
           refine Algebra.IsInvariant.isInvariant (G := G) _ fun g ↦ ?_
           rw [← Polynomial.coeff_smul, Finset.smul_prod']
           congr 1
           simp only [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul]
           exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ ↦ rfl)
    obtain ⟨f, hf1, -, hf2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hmem hmonic
    exact ⟨f, hf1, hf2⟩
  choose f hfmap hfmonic using hlift
  obtain ⟨φ, hφ⟩ : ∃ φ : B →+* L, ∀ b, φ b = algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q b) :=
    ⟨(algebraMap (B ⧸ Q) L).comp (Ideal.Quotient.mk Q), fun _ ↦ rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A →+* K, ∀ a, ψ a = algebraMap (A ⧸ P) K (Ideal.Quotient.mk P a) :=
    ⟨(algebraMap (A ⧸ P) K).comp (Ideal.Quotient.mk P), fun _ ↦ rfl⟩
  have hcomm : (algebraMap K L).comp ψ = φ.comp (algebraMap A B) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, hψ, hφ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L]
    all_goals first | rfl | simp
  have hq : ∀ b : B, ((f b).map ψ).map (algebraMap K L) =
      ∏ g : G, (Polynomial.X - Polynomial.C (φ (g • b))) := by
    intro b
    rw [Polynomial.map_map, hcomm, ← Polynomial.map_map, hfmap]
    first
      | (rw [Polynomial.map_prod]; simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]; done)
      | simp
  have hroot : ∀ b : B, Polynomial.aeval (φ b) ((f b).map ψ) = 0 := by
    intro b
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have hne : ∀ b : B, (f b).map ψ ≠ 0 := fun b ↦ ((hfmonic b).map ψ).ne_zero
  have hmemE : ∀ b : B, φ b ∈ IntermediateField.adjoin K (((f b).map ψ).rootSet L) := by
    intro b
    have hr : φ b ∈ ((f b).map ψ).rootSet L := by
      first
        | exact Polynomial.mem_rootSet.mpr ⟨hne b, hroot b⟩
        | exact (Polynomial.mem_rootSet_of_ne (Polynomial.map_ne_zero (hne b))).mpr (hroot b)
        | simp [Polynomial.mem_rootSet, hne b, hroot b]
    exact IntermediateField.subset_adjoin K _ hr
  have hnormal : ∀ b : B, Normal K (IntermediateField.adjoin K (((f b).map ψ).rootSet L)) := by
    intro b
    have hs : Polynomial.IsSplittingField K
        (IntermediateField.adjoin K (((f b).map ψ).rootSet L)) ((f b).map ψ) := by
      apply IntermediateField.adjoin_rootSet_isSplittingField
      first
        | (rw [← Polynomial.splits_id_iff_splits, hq]; apply Polynomial.splits_prod; intro _ _; apply Polynomial.splits_X_sub_C)
        | (rw [hq]; apply Polynomial.Splits.prod; intro _ _; apply Polynomial.Splits.X_sub_C)
        | (rw [hq]; apply Polynomial.splits_prod; intro _ _; apply Polynomial.splits_X_sub_C)
        | (rw [hq]; apply Polynomial.Factors.prod; intro _ _; apply Polynomial.Factors.X_sub_C)
        | (rw [hq]; simp; done)
        | (rw [← Polynomial.splits_id_iff_splits, hq]; simp; done)
        | (rw [hq]; aesop)
    exact Normal.of_isSplittingField ((f b).map ψ)
  have hN : Normal K (⨆ b : B, IntermediateField.adjoin K (((f b).map ψ).rootSet L) :
      IntermediateField K L) := by
    first
      | exact inferInstance
      | exact IntermediateField.normal_iSup _
      | exact IntermediateField.normal_iSup (h := hnormal) _
  have htop : (⨆ b : B, IntermediateField.adjoin K (((f b).map ψ).rootSet L)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hmem : ∀ w : B ⧸ Q, algebraMap (B ⧸ Q) L w ∈
        ⨆ b : B, IntermediateField.adjoin K (((f b).map ψ).rootSet L) := by
      intro w
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
      rw [← hφ]
      exact le_iSup (fun b : B ↦ IntermediateField.adjoin K (((f b).map ψ).rootSet L)) b (hmemE b)
    obtain ⟨⟨u, v⟩, huv⟩ := IsLocalization.surj (nonZeroDivisors (B ⧸ Q)) x
    have hv : algebraMap (B ⧸ Q) L (v : B ⧸ Q) ≠ 0 := by
      first
        | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors v.2
        | exact (map_ne_zero_iff _ (IsFractionRing.injective (B ⧸ Q) L)).mpr
            (nonZeroDivisors.ne_zero v.2)
    have hx : x = algebraMap (B ⧸ Q) L u / algebraMap (B ⧸ Q) L v := by
      rw [eq_div_iff hv]
      exact huv
    rw [hx]
    first
      | exact IntermediateField.div_mem _ (hmem u) (hmem v)
      | exact div_mem (hmem u) (hmem v)
      | (rw [div_eq_mul_inv]; exact mul_mem (hmem u) (inv_mem (hmem v)))
  haveI := hN
  exact Normal.of_algEquiv ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
