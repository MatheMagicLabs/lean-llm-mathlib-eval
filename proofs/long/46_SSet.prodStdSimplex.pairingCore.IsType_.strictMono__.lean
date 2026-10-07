/-
Machine-generated proof, verified by Lean.

Theorem:      SSet.prodStdSimplex.pairingCore.IsType₂.strictMono_φ
Source:       Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/UnionProd.lean, line 342
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  34 tactic steps; area: AlgebraicTopology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma strictMono_φ : StrictMono (φ x hd) := by
  have hs : StrictMono (objEquiv (x.cast hd).simplex) := by
    first
    | exact (objEquiv (x.cast hd).simplex).monotone.strictMono_of_injective
        ((nonDegenerate_iff_injective_objEquiv _).1 (x.cast hd).nonDegenerate)
    | exact (nonDegenerate_iff_strictMono_objEquiv _).1 (x.cast hd).nonDegenerate
    | exact (objEquiv (x.cast hd).simplex).monotone.strictMono_of_injective
        ((nonDegenerate_iff_injective _).1 (x.cast hd).nonDegenerate)
    | exact (nonDegenerate_iff_strictMono _).1 (x.cast hd).nonDegenerate
    | exact (strictMono_objEquiv_iff _).2 (x.cast hd).nonDegenerate
    | exact strictMono_of_nonDegenerate (x.cast hd).nonDegenerate
    | exact (objEquiv (x.cast hd).simplex).monotone.strictMono_of_injective
        (injective_of_nonDegenerate (x.cast hd).nonDegenerate)
  refine Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_
  rcases lt_trichotomy i (min x hd) with h | rfl | h
  · have h1 : i.castSucc < (min x hd).castSucc := Fin.castSucc_lt_castSucc_iff.2 h
    rw [φ_of_lt x hd _ h1]
    rcases (Fin.castSucc_lt_iff_succ_le.1 h1).lt_or_eq with h2 | h2
    · rw [φ_of_lt x hd _ h2]
      apply hs
      first
      | exact Fin.castPred_lt_castPred_iff.2 (Fin.castSucc_lt_succ i)
      | exact Fin.castPred_lt_castPred_iff.2 Fin.castSucc_lt_succ
      | simp [Fin.lt_iff_val_lt_val]
    · rw [h2, φ_castSucc]
      try simp only [Fin.castPred_castSucc]
      have hμ : min x hd ≠ 0 := by
        intro h0
        rw [h0] at h
        exact Fin.not_lt_zero i h
      obtain ⟨l, hl⟩ := Fin.eq_succ_of_ne_zero hμ
      have hli : l.castSucc = i := by
        rw [hl, ← Fin.succ_castSucc] at h2
        exact (Fin.succ_injective _ h2).symm
      have hA : (x.cast hd).simplex.1 i ≤ k.castSucc := (simplex_fst_le_castSucc_iff x hd i).2 h
      have hB : (x.cast hd).simplex.2 i ≤ (x.cast hd).simplex.2 (min x hd) :=
        stdSimplex.monotone_apply (x.cast hd).simplex.2 h.le
      refine lt_of_le_of_ne ?_ ?_
      · first
        | exact Prod.le_def.2 ⟨hA, hB⟩
        | exact ⟨hA, hB⟩
        | exact Prod.le_def.2 ⟨by simpa using hA, by simpa using hB⟩
        | (constructor <;> simpa [hA, hB])
      · intro hq
        apply hx d hd (min x hd)
        rw [hl, isIndex_succ, hli, ← hl]
        refine ⟨?_, simplex_fst_min x hd, ?_⟩
        · first
          | exact congrArg Prod.fst hq
          | simpa using congrArg Prod.fst hq
        · first
          | exact (congrArg Prod.snd hq).symm
          | simpa using (congrArg Prod.snd hq).symm
  · rw [Prod.lt_iff]
    left
    refine ⟨?_, (φ_succ_snd x hd).ge⟩
    rw [φ_succ_fst, φ_castSucc]
    first
    | exact Fin.castSucc_lt_succ k
    | exact Fin.castSucc_lt_succ
    | simp
  · have h1 : (min x hd).castSucc < i.castSucc := Fin.castSucc_lt_castSucc_iff.2 h
    have h2 : (min x hd).castSucc < i.succ := by
      first
      | exact h1.trans (Fin.castSucc_lt_succ i)
      | exact h1.trans Fin.castSucc_lt_succ
    rw [φ_of_gt x hd _ h1, φ_of_gt x hd _ h2]
    apply hs
    first
    | exact Fin.pred_lt_pred_iff.2 (Fin.castSucc_lt_succ i)
    | exact Fin.pred_lt_pred_iff.2 Fin.castSucc_lt_succ
    | simp [Fin.lt_iff_val_lt_val]
