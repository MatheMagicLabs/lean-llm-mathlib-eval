/-
Machine-generated proof, verified by Lean.

Theorem:      CartanMatrix.Realisation.isIrreducible_toRootPairing
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Cartan/Realisation.lean, line 526
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  36 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma isIrreducible_toRootPairing [Nonempty n] {k V W : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (rl : Realisation n k V W)
    (hr : span k (range rl.sRoot) = ⊤)
    (hA' : rl.matrix.IsIndecomposable) :
    rl.toRootPairing.IsIrreducible := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty n›
  haveI : Nontrivial V := nontrivial_of_ne _ _ (rl.lin_ind_sRoot.ne_zero j₀)
  apply RootPairing.IsIrreducible.mk'
  intro q hq hq0
  have key : ∀ j : n, ∀ x ∈ q, rl.sRoot j ∉ q → rl.pairing x (rl.sCoroot j) = 0 := by
    intro j x hx hj
    by_contra hc
    apply hj
    have h1 : rl.toRootPairing.reflection ⟨_, rl.sPair_mem_idx j⟩ x ∈ q := by
      first
        | exact hq ⟨_, rl.sPair_mem_idx j⟩ hx
        | exact (Module.End.mem_invtSubmodule _).mp (hq ⟨_, rl.sPair_mem_idx j⟩) hx
        | exact Module.End.mem_invtSubmodule_iff_forall_mem_of_mem.mp
            (hq ⟨_, rl.sPair_mem_idx j⟩) x hx
    have h2 : rl.toRootPairing.reflection ⟨_, rl.sPair_mem_idx j⟩ x =
        x - (rl.pairing x (rl.sCoroot j)) • rl.sRoot j := by
      first
        | rfl
        | simp [RootPairing.reflection_apply]
        | simp [RootPairing.reflection_apply, RootPairing.coroot']
    rw [h2] at h1
    have h3 : (rl.pairing x (rl.sCoroot j)) • rl.sRoot j ∈ q := by
      have h4 := sub_mem hx h1
      rwa [sub_sub_cancel] at h4
    have h5 := q.smul_mem (rl.pairing x (rl.sCoroot j))⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h5
  by_cases hall : ∀ j, rl.sRoot j ∈ q
  · apply top_unique
    rw [← hr, Submodule.span_le]
    rintro - ⟨j, rfl⟩
    exact hall j
  push_neg at hall
  obtain ⟨j₁, hj₁⟩ := hall
  by_cases hnone : ∀ j, rl.sRoot j ∉ q
  · exfalso
    apply hq0
    apply bot_unique
    intro x hx
    rw [Submodule.mem_bot]
    have hx0 : x - 0 ∈ span k (range rl.flip.sCoroot) := by
      have hfl : rl.flip.sCoroot = rl.sRoot := rfl
      rw [hfl, hr]
      exact Submodule.mem_top
    exact (rl.flip.eq_iff_forall_pairing_sRoot_eq hx0).mpr fun j => by
      change rl.pairing x (rl.sCoroot j) = rl.pairing 0 (rl.sCoroot j)
      first
        | rw [key j x hx (hnone j), map_zero, LinearMap.zero_apply]
        | simp [key j x hx (hnone j)]
  push_neg at hnone
  obtain ⟨j₂, hj₂⟩ := hnone
  exfalso
  let e := (Equiv.sumCongr (Finite.equivFin {t // rl.sRoot t ∉ q}).symm
    (Finite.equivFin {t // ¬ rl.sRoot t ∉ q}).symm).trans (Equiv.sumCompl fun t => rl.sRoot t ∉ q)
  have h21 : (rl.matrix.submatrix e e).toBlocks₂₁ = 0 := by
    ext r c
    change rl.matrix ((Finite.equivFin {t // ¬ rl.sRoot t ∉ q}).symm r).1
      ((Finite.equivFin {t // rl.sRoot t ∉ q}).symm c).1 = 0
    have h := rl.pairingMatrix ((Finite.equivFin {t // ¬ rl.sRoot t ∉ q}).symm r).1
      ((Finite.equivFin {t // rl.sRoot t ∉ q}).symm c).1
    rw [key _ _ (not_not.mp ((Finite.equivFin {t // ¬ rl.sRoot t ∉ q}).symm r).2)
      ((Finite.equivFin {t // rl.sRoot t ∉ q}).symm c).2] at h
    exact_mod_cast h.symm
  have heq : rl.matrix = reindex e e (fromBlocks (rl.matrix.submatrix e e).toBlocks₁₁
      (rl.matrix.submatrix e e).toBlocks₁₂ 0 (rl.matrix.submatrix e e).toBlocks₂₂) := by
    rw [← h21, fromBlocks_toBlocks, reindex_apply, submatrix_submatrix, Equiv.self_comp_symm,
      submatrix_id_id]
  rcases hA' _ _ _ _ _ e heq with h | h
  · haveI : Nonempty {t // rl.sRoot t ∉ q} := ⟨⟨j₁, hj₁⟩⟩
    have h0 : 0 < Nat.card {t // rl.sRoot t ∉ q} := Nat.card_pos
    exact h0.ne' h
  · haveI : Nonempty {t // ¬ rl.sRoot t ∉ q} := ⟨⟨j₂, not_not.mpr hj₂⟩⟩
    have h0 : 0 < Nat.card {t // ¬ rl.sRoot t ∉ q} := Nat.card_pos
    exact h0.ne' h
