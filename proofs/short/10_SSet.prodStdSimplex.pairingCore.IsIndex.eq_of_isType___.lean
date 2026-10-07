/-
Machine-generated proof, verified by Lean.

Theorem:      SSet.prodStdSimplex.pairingCore.IsIndex.eq_of_isType₂_δ
Source:       Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/UnionProd.lean, line 454
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  13 tactic steps; area: AlgebraicTopology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma eq_of_isType₂_δ {u : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (hu : IsType₂ u) (i : Fin (d + 2))
    (hu' : S.mk u.simplex = S.mk (((Δ[m + 1] ⊗ Δ[n])).δ i (x.cast hd).simplex)) :
    i = l.castSucc ∨ i = l.succ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h1, h2⟩ := hne
  have hi1 : i.val ≠ l.val := fun h => h1 (Fin.ext h)
  have hi2 : i.val ≠ l.val + 1 := fun h => h2 (Fin.ext h)
  have hlt := l.isLt
  have hit := i.isLt
  obtain ⟨j, hj1, hj2⟩ : ∃ j : Fin d, i.succAbove j.castSucc = l.castSucc ∧
      i.succAbove j.succ = l.succ := by
    rcases Nat.lt_or_gt_of_ne hi1 with h | h
    · refine ⟨⟨l.val - 1, by omega⟩, ?_, ?_⟩
      · rw [Fin.succAbove_of_le_castSucc]
        · exact Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc] <;> omega)
        · rw [Fin.le_def]
          simp only [Fin.coe_castSucc] <;> omega
      · rw [Fin.succAbove_of_le_castSucc]
        · exact Fin.ext (by simp only [Fin.val_succ] <;> omega)
        · rw [Fin.le_def]
          simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega
    · refine ⟨⟨l.val, by omega⟩, ?_, ?_⟩
      · rw [Fin.succAbove_of_castSucc_lt]
        · exact Fin.ext (by simp only [Fin.coe_castSucc] <;> omega)
        · rw [Fin.lt_def]
          simp only [Fin.coe_castSucc] <;> omega
      · rw [Fin.succAbove_of_castSucc_lt]
        · exact Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega)
        · rw [Fin.lt_def]
          simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega
  obtain ⟨⟨@⟨du, su⟩, hnd⟩, hnm⟩ := u
  have hdu : d = du := by
    first
      | exact (congrArg S.dim hu').symm
      | exact (S.dim_eq_of_mk_eq hu').symm
  subst hdu
  have hsu : su = (Δ[m + 1] ⊗ Δ[n]).δ i (x.cast hd).simplex := by
    first
      | exact eq_of_heq (S.mk.inj hu').2
      | (injection hu' with h3 h4
         exact eq_of_heq h4)
  subst hsu
  first
    | refine hu d rfl j.succ ?_
    | refine hu _ rfl j.succ ?_
  first
    | rw [isIndex_succ]
    | simp only [isIndex_succ]
  first
    | (simp only [S.cast_simplex_rfl, Monoidal.tensorObj_obj, prod_δ_fst, prod_δ_snd,
        stdSimplex.δ_apply, hj1, hj2]
       exact ⟨hl.simplex_fst_castSucc, hl.simplex_fst_succ, hl.simplex_snd_succ⟩)
    | (simp only [S.cast_simplex_rfl, Monoidal.tensorObj_obj, prod_δ_fst, prod_δ_snd,
        stdSimplex.δ_apply, hj1, hj2, hl.simplex_fst_castSucc, hl.simplex_fst_succ,
        hl.simplex_snd_succ, and_self])
    | simp [prod_δ_fst, prod_δ_snd, stdSimplex.δ_apply, hj1, hj2, hl.simplex_fst_castSucc,
        hl.simplex_fst_succ, hl.simplex_snd_succ]
