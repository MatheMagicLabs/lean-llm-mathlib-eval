/-
Machine-generated proof, verified by Lean.

Theorem:      SimpleGraph.egirth_top
Source:       Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Girth.lean, line 76
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  8 tactic steps; area: Combinatorics
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem egirth_top (h : 3 ≤ ENat.card α) : egirth (⊤ : SimpleGraph α) = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rcases finite_or_infinite α with hfin | hinf
    · have := Fintype.ofFinite α
      have h3 : 3 ≤ Fintype.card α := by
        first
          | (rw [ENat.card_eq_coe_fintype_card] at h; exact_mod_cast h)
          | simpa using h
      exact Fintype.two_lt_card_iff.1 (by omega)
    · exact ⟨Infinite.natEmbedding α 0, Infinite.natEmbedding α 1, Infinite.natEmbedding α 2,
        (Infinite.natEmbedding α).injective.ne (by decide),
        (Infinite.natEmbedding α).injective.ne (by decide),
        (Infinite.natEmbedding α).injective.ne (by decide)⟩
  refine le_antisymm ?_ three_le_egirth
  have h1 : (⊤ : SimpleGraph α).Adj a b := by simpa using hab
  have h2 : (⊤ : SimpleGraph α).Adj b c := by simpa using hbc
  have h3 : (⊤ : SimpleGraph α).Adj c a := by simpa using hac.symm
  have hw : (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil))).IsCycle := by
    first
      | (simp [Walk.cons_isCycle_iff, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, Sym2.eq_iff];
          done)
      | (simp [Walk.cons_isCycle_iff, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]; done)
      | (simp [Walk.isCycle_def, Walk.isTrail_def, hab, hac, hbc, hab.symm, hac.symm, hbc.symm,
          Sym2.eq_iff]; done)
  first
    | simpa using hw.egirth_le_length
    | exact hw.egirth_le_length.trans_eq rfl
