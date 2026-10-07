/-
Machine-generated proof, verified by Lean.

Theorem:      SSet.PtSimplex.MulStruct.assocAux.isCompatible_α
Source:       Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean, line 363
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  45 tactic steps; area: AlgebraicTopology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma isCompatible_α : horn.IsCompatible (fun j hj ↦ α h₀₂ h₁₃ h j hj) := by
  have G1 : ∀ (J : Fin (n + 3)) (hJ : J ≠ i.castSucc.castSucc.succ) (k : Fin (n + 2)),
      i.succ.succ < k → stdSimplex.δ k ≫ α h₀₂ h₁₃ h J hJ = const x := by
    intro J hJ k hk
    first
    | dsimp only [α]
    | unfold α
    | simp only [α]
    split_ifs
    all_goals
      first
      | exact h₁₃.δ_map_of_gt k hk
      | exact h.δ_map_of_gt k hk
      | exact h₀₂.δ_map_of_gt k hk
      | exact comp_const _ _
      | rfl
      | simp
  have G2 : ∀ (J : Fin (n + 3)) (hJ : J ≠ i.castSucc.castSucc.succ) (k : Fin (n + 2)),
      k < i.castSucc.castSucc → stdSimplex.δ k ≫ α h₀₂ h₁₃ h J hJ = const x := by
    intro J hJ k hk
    first
    | dsimp only [α]
    | unfold α
    | simp only [α]
    split_ifs
    all_goals
      first
      | exact h₁₃.δ_map_of_lt k hk
      | exact h.δ_map_of_lt k hk
      | exact h₀₂.δ_map_of_lt k hk
      | exact comp_const _ _
      | rfl
      | simp
  have e₂ : ∀ (J : Fin (n + 3)) (hJ : J ≠ i.castSucc.castSucc.succ),
      J = i.castSucc.succ.succ → α h₀₂ h₁₃ h J hJ = h.map := by
    rintro J hJ rfl
    exact α_castSucc_succ_succ h₀₂ h₁₃ h
  have main : ∀ (j k : Fin (n + 2)) (hj : j.castSucc ≠ i.castSucc.castSucc.succ)
      (hk : k.succ ≠ i.castSucc.castSucc.succ), j ≤ k →
      stdSimplex.δ k ≫ α h₀₂ h₁₃ h j.castSucc hj = stdSimplex.δ j ≫ α h₀₂ h₁₃ h k.succ hk := by
    intro j k hj hk hjk
    by_cases hk' : i.succ.succ < k
    · rw [G1 _ _ k hk', α_of_gt h₀₂ h₁₃ h k.succ
        (by first | exact Fin.succ_lt_succ_iff.2 hk' | grind), comp_const]
    by_cases hj' : j < i.castSucc.castSucc
    · rw [G2 _ _ j hj', α_of_lt h₀₂ h₁₃ h j.castSucc
        (by first | exact Fin.castSucc_lt_castSucc_iff.2 hj' | grind), comp_const]
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (j = i.castSucc.castSucc ∧ k = i.castSucc.succ) ∨
        (j = i.castSucc.castSucc ∧ k = i.succ.succ) ∨ (j = i.succ.succ ∧ k = i.succ.succ) := by
      first
      | grind
      | (simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ,
          Fin.coe_castSucc, ne_eq, not_lt] at hj hk hjk hk' hj' ⊢ <;> omega)
      | (simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at hj hk hjk hk' hj' ⊢
          <;> omega)
    · simp only [α_castSucc_castSucc_castSucc, α_castSucc_succ_succ,
        MulStruct.δ_succ_castSucc_map, MulStruct.δ_castSucc_castSucc_map]
    · simp only [α_castSucc_castSucc_castSucc, α_succ_succ_succ,
        MulStruct.δ_succ_succ_map, MulStruct.δ_castSucc_castSucc_map]
    · rw [e₂ (i.succ.succ.castSucc) _ (by first | grind | exact Fin.ext (by simp))]
      simp only [α_succ_succ_succ, MulStruct.δ_succ_succ_map]
  first
  | intro j k hj hk hjk
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last
      (by first | exact Fin.ne_last_of_lt hjk | grind)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero
      (by first | exact Fin.ne_zero_of_lt hjk | grind)
    simp only [Fin.castPred_castSucc, Fin.pred_succ]
    first
    | exact main j k hj hk (Fin.castSucc_lt_succ_iff.1 hjk)
    | exact (main j k hj hk (Fin.castSucc_lt_succ_iff.1 hjk)).symm
    | exact main j k hj hk (by grind)
    | exact (main j k hj hk (by grind)).symm
  | intro j k
    intros
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last
      (by first | exact Fin.ne_last_of_lt ‹_› | grind)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero
      (by first | exact Fin.ne_zero_of_lt ‹_› | grind)
    simp only [Fin.castPred_castSucc, Fin.pred_succ]
    first
    | exact main j k ‹_› ‹_› (by grind)
    | exact (main j k ‹_› ‹_› (by grind)).symm
  | intro j k
    intros
    try beta_reduce
    first
    | exact main j k ‹_› ‹_› ‹_›
    | exact (main j k ‹_› ‹_› ‹_›).symm
    | exact main j k ‹_› ‹_› (by grind)
    | exact (main j k ‹_› ‹_› (by grind)).symm
  | intro k j
    intros
    try beta_reduce
    first
    | exact main j k ‹_› ‹_› ‹_›
    | exact (main j k ‹_› ‹_› ‹_›).symm
    | exact main j k ‹_› ‹_› (by grind)
    | exact (main j k ‹_› ‹_› (by grind)).symm
