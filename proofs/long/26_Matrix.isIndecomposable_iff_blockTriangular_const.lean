/-
Machine-generated proof, verified by Lean.

Theorem:      Matrix.isIndecomposable_iff_blockTriangular_const
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Block.lean, line 247
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  39 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma isIndecomposable_iff_blockTriangular_const [Nontrivial α] [Finite m] [Zero R]
    (M : Matrix m m R) :
    M.IsIndecomposable ↔ ∀ b : m → α, M.BlockTriangular b → ∃ a, b = const m a := by
  classical
  constructor
  · intro hM b hb
    by_contra! hne
    rcases isEmpty_or_nonempty m with hm | hm
    · obtain ⟨a⟩ : Nonempty α := inferInstance
      exact hne a (funext fun i => (IsEmpty.false i).elim)
    obtain ⟨x⟩ := hm
    obtain ⟨y, hy⟩ : ∃ y, b y ≠ b x := by
      by_contra! h'
      exact hne (b x) (funext h')
    obtain ⟨u, v, huv⟩ : ∃ u v, b u < b v := by
      rcases lt_trichotomy (b x) (b y) with h | h | h
      · exact ⟨x, y, h⟩
      · exact absurd h.symm hy
      · exact ⟨y, x, h⟩
    let e := (Equiv.sumCongr (Finite.equivFin {k // b k ≤ b u}).symm
      (Finite.equivFin {k // ¬ b k ≤ b u}).symm).trans (Equiv.sumCompl fun k => b k ≤ b u)
    have h21 : (M.submatrix e e).toBlocks₂₁ = 0 := by
      ext r c
      have hc1 : b (e (Sum.inl c)) ≤ b u := ((Finite.equivFin {k // b k ≤ b u}).symm c).2
      have hr1 : ¬ b (e (Sum.inr r)) ≤ b u := ((Finite.equivFin {k // ¬ b k ≤ b u}).symm r).2
      exact hb (lt_of_le_of_lt hc1 (not_le.mp hr1))
    have heq : M = reindex e e (fromBlocks (M.submatrix e e).toBlocks₁₁
        (M.submatrix e e).toBlocks₁₂ 0 (M.submatrix e e).toBlocks₂₂) := by
      first
        | rw [← h21, fromBlocks_toBlocks, reindex_apply, submatrix_submatrix,
            Equiv.self_comp_symm, submatrix_id_id]
        | (rw [← h21, fromBlocks_toBlocks]; ext p q; simp)
    rcases hM _ _ _ _ _ e heq with h | h
    · have : Nonempty {k // b k ≤ b u} := ⟨⟨u, le_rfl⟩⟩
      have h0 : 0 < Nat.card {k // b k ≤ b u} := Nat.card_pos
      exact h0.ne' h
    · have : Nonempty {k // ¬ b k ≤ b u} := ⟨⟨v, not_le.mpr huv⟩⟩
      have h0 : 0 < Nat.card {k // ¬ b k ≤ b u} := Nat.card_pos
      exact h0.ne' h
  · intro h i j A B D e hM
    obtain ⟨a₁, a₂, ha⟩ := exists_pair_lt α
    obtain ⟨a, hab⟩ := h (fun k => Sum.elim (fun _ => a₁) (fun _ => a₂) (e.symm k)) (by
      intro r c hrc
      obtain ⟨x, rfl⟩ := e.surjective r
      obtain ⟨y, rfl⟩ := e.surjective c
      simp only [Equiv.symm_apply_apply] at hrc
      rw [hM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rcases x with x | x <;> rcases y with y | y
      · exact absurd hrc (lt_irrefl _)
      · exact (lt_asymm ha hrc).elim
      · simp
      · exact absurd hrc (lt_irrefl _))
    by_contra! hij
    have h1 : Sum.elim (fun _ => a₁) (fun _ => a₂)
        (e.symm (e (Sum.inl ⟨0, Nat.pos_of_ne_zero hij.1⟩))) = a :=
      congr_fun hab (e (Sum.inl ⟨0, Nat.pos_of_ne_zero hij.1⟩))
    have h2 : Sum.elim (fun _ => a₁) (fun _ => a₂)
        (e.symm (e (Sum.inr ⟨0, Nat.pos_of_ne_zero hij.2⟩))) = a :=
      congr_fun hab (e (Sum.inr ⟨0, Nat.pos_of_ne_zero hij.2⟩))
    rw [Equiv.symm_apply_apply] at h1 h2
    exact ha.ne (h1.trans h2.symm)
