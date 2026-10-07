/-
Machine-generated proof, verified by Lean.

Theorem:      SimpleGraph.turanNumber_eq
Source:       Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean, line 373
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  31 tactic steps; area: Combinatorics
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem turanNumber_eq {n r : ℕ} :
    turanNumber n r = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  have base_top : ∀ m : ℕ, turanGraph m r = ⊤ → turanNumber m r = m.choose 2 := by
    intro m hm
    show (turanGraph m r).edgeFinset.card = m.choose 2
    have e : (turanGraph m r).edgeFinset = (⊤ : SimpleGraph (Fin m)).edgeFinset := by
      ext x
      first
        | simp only [mem_edgeFinset, hm]
        | simp [hm]
    rw [e]
    first
      | rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
      | (convert card_edgeFinset_top_eq_card_choose_two (V := Fin m) using 2 <;> simp)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [Nat.mod_zero, Nat.sub_self, Nat.zero_mul, Nat.zero_div, Nat.zero_add]
    exact base_top n turanGraph_zero
  · have base : ∀ m : ℕ, m < r →
        turanNumber m r = (m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2 := by
      intro m hlt
      have htop : turanGraph m r = ⊤ := by
        first
          | exact turanGraph_eq_top.mpr (Or.inr hlt.le)
          | (ext v w; simp only [turanGraph_adj, top_adj, Nat.mod_eq_of_lt (lt_trans v.2 hlt), Nat.mod_eq_of_lt (lt_trans w.2 hlt), ne_eq, Fin.val_inj])
      rw [Nat.mod_eq_of_lt hlt, Nat.sub_self, Nat.zero_mul, Nat.zero_div, Nat.zero_add]
      exact base_top m htop
    have step : ∀ m : ℕ,
        turanNumber m r = (m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2 →
        turanNumber (m + r) r = ((m + r) ^ 2 - ((m + r) % r) ^ 2) * (r - 1) / (2 * r) +
          ((m + r) % r).choose 2 := by
      intro m hm
      have h2r : 0 < 2 * r := by omega
      have hc : r.choose 2 * 2 = r * (r - 1) := by
        rw [Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
      have h5 : (m + r) ^ 2 = m ^ 2 + 2 * m * r + r ^ 2 := by
        first
          | exact add_sq m r
          | exact add_pow_two m r
          | grind
      have h6 : (m % r) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.mod_le m r) 2
      have e1 : (m + r) ^ 2 - (m % r) ^ 2 = (m ^ 2 - (m % r) ^ 2) + (2 * m * r + r ^ 2) := by
        omega
      have f1 : ((m + r) ^ 2 - (m % r) ^ 2) * (r - 1) =
          (m ^ 2 - (m % r) ^ 2) * (r - 1) + (2 * m * r + r ^ 2) * (r - 1) := by
        rw [e1, Nat.add_mul]
      have f2 : (2 * m * r + r ^ 2) * (r - 1) = 2 * m * r * (r - 1) + r ^ 2 * (r - 1) :=
        Nat.add_mul _ _ _
      have f3 : 2 * r * (m * (r - 1) + r.choose 2) =
          2 * r * (m * (r - 1)) + 2 * r * r.choose 2 :=
        Nat.mul_add _ _ _
      have g1 : 2 * m * r * (r - 1) = 2 * (r * (m * (r - 1))) := by
        rw [Nat.mul_assoc (2 * m) r (r - 1), Nat.mul_assoc 2 m (r * (r - 1)),
          Nat.mul_left_comm m r (r - 1)]
      have g2 : 2 * r * (m * (r - 1)) = 2 * (r * (m * (r - 1))) := Nat.mul_assoc 2 r _
      have g3 : r ^ 2 * (r - 1) = r * (r * (r - 1)) := by
        first
          | rw [pow_two, Nat.mul_assoc]
          | rw [sq, Nat.mul_assoc]
          | rw [Nat.pow_two, Nat.mul_assoc]
      have g4 : 2 * r * r.choose 2 = r * (r * (r - 1)) := by
        rw [Nat.mul_comm 2 r, Nat.mul_assoc r 2 (r.choose 2), Nat.mul_comm 2 (r.choose 2), hc]
      have key : ((m + r) ^ 2 - (m % r) ^ 2) * (r - 1) =
          (m ^ 2 - (m % r) ^ 2) * (r - 1) + 2 * r * (m * (r - 1) + r.choose 2) := by
        omega
      rw [turanNumber_add, hm, Nat.add_mod_right, key]
      first
        | rw [Nat.add_mul_div_left _ _ h2r]
        | rw [Nat.add_mul_div_left h2r]
      omega
    have main : ∀ N m : ℕ, m ≤ N →
        turanNumber m r = (m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2 := by
      intro N
      induction N with
      | zero =>
        intro m hm
        exact base m (by omega)
      | succ N ih =>
        intro m hm
        rcases Nat.lt_or_ge m r with hlt | hge
        · exact base m hlt
        · obtain ⟨k, rfl⟩ : ∃ k, m = k + r := ⟨m - r, by omega⟩
          exact step k (ih k (by omega))
    exact main n n le_rfl
