/-
Machine-generated proof, verified by Lean.

Theorem:      Ideal.ramificationIdx'_eq_one_of_map_localization
Source:       Mathlib @ d0a050ad6, Mathlib/NumberTheory/RamificationInertia/Ramification.lean, line 214
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  8 tactic steps; area: NumberTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma ramificationIdx'_eq_one_of_map_localization
    {p : Ideal R} {P : Ideal S} [P.IsPrime] [IsNoetherianRing S]
    (hpP : map (algebraMap R S) p ≤ P) (hp : P ≠ ⊥) (hp' : P.primeCompl ≤ nonZeroDivisors S)
    (H : p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P)) :
    ramificationIdx' p P = 1 := by
  by_contra hne
  have h2 : p.map (algebraMap R S) ≤ P ^ 2 := (ramificationIdx'_ne_one_iff hpP).mp hne
  have hmap : P.map (algebraMap S (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    first
      | exact Localization.AtPrime.map_eq_maximalIdeal P
      | exact Localization.AtPrime.map_eq_maximalIdeal
      | exact IsLocalization.AtPrime.map_eq_maximalIdeal P _
      | rw [Localization.AtPrime.map_eq_maximalIdeal]
      | rw [IsLocalization.AtPrime.map_eq_maximalIdeal]
  have htower : p.map (algebraMap R (Localization.AtPrime P)) =
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime P)) := by
    first
      | rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      | rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime P), Ideal.map_map]
      | simp [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 2 := by
    calc IsLocalRing.maximalIdeal (Localization.AtPrime P)
        _ = p.map (algebraMap R (Localization.AtPrime P)) := H.symm
        _ = (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime P)) := htower
        _ ≤ (P ^ 2).map (algebraMap S (Localization.AtPrime P)) := Ideal.map_mono h2
        _ = (P.map (algebraMap S (Localization.AtPrime P))) ^ 2 := by rw [Ideal.map_pow]
        _ = IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 2 := by rw [hmap]
  have hfg : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).FG := by
    first
      | exact IsNoetherian.noetherian _
      | (rw [← hmap]; exact Ideal.FG.map (IsNoetherian.noetherian P) _)
      | (haveI : IsNoetherianRing (Localization.AtPrime P) := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance; exact IsNoetherian.noetherian _)
  have hjac : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ Ideal.jacobson ⊥ := by
    first
      | exact IsLocalRing.maximalIdeal_le_jacobson _
      | exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      | exact le_sInf fun J hJ => le_of_eq (IsLocalRing.eq_maximalIdeal hJ.2).symm
  have hbot : IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg ?_ hjac
    first
      | exact hm.trans_eq (pow_two _)
      | (rw [Ideal.smul_eq_mul, ← pow_two]; exact hm)
      | (rw [smul_eq_mul, ← pow_two]; exact hm)
  have hinj : Function.Injective (algebraMap S (Localization.AtPrime P)) := by
    first
      | exact IsLocalization.injective (Localization.AtPrime P) hp'
      | exact IsLocalization.injective _ hp'
      | exact IsLocalization.injective hp'
  have hc : Ideal.comap (algebraMap S (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = P := by
    first
      | exact Localization.AtPrime.comap_maximalIdeal P
      | exact Localization.AtPrime.comap_maximalIdeal
      | exact IsLocalization.AtPrime.comap_maximalIdeal _ P
      | simp
  apply hp
  rw [← hc, hbot]
  first
    | exact Ideal.comap_bot_of_injective _ hinj
    | exact Ideal.comap_bot_of_injective hinj
    | exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
