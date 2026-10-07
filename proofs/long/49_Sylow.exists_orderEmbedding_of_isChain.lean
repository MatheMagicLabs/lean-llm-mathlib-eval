/-
Machine-generated proof, verified by Lean.

Theorem:      Sylow.exists_orderEmbedding_of_isChain
Source:       Mathlib @ d0a050ad6, Mathlib/GroupTheory/Sylow.lean, line 724
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  35 tactic steps; area: GroupTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_orderEmbedding_of_isChain [Finite G] {p n : ℕ} (hp : p.Prime)
    (hdvd : p ^ n ∣ Nat.card G) {s : Set (Subgroup G)} (hchain : IsChain (· ≤ ·) s)
    (hcard : ∀ H ∈ s, Nat.card H ∣ p ^ n) :
    ∃ f : Fin (n + 1) ↪o Subgroup G, s ⊆ Set.range f ∧ ∀ k, Nat.card (f k) = p ^ k.val := by
  have hmax : ∀ t : Set (Subgroup G), IsChain (· ≤ ·) t →
      ∃ M : Subgroup G, (M = ⊥ ∨ M ∈ t) ∧ ∀ H ∈ t, H ≤ M := by
    intro t ht
    by_cases hne : t.Nonempty
    · obtain ⟨M, hM, hMmax⟩ : ∃ M ∈ t, ∀ H ∈ t, Nat.card H ≤ Nat.card M := by
        first
          | exact Set.exists_max_image t (fun H => Nat.card H) t.toFinite hne
          | obtain ⟨M, hM, hMmax⟩ := Finset.exists_max_image t.toFinite.toFinset
                (fun H : Subgroup G => Nat.card H) (by simpa using hne)
            exact ⟨M, by simpa using hM, fun H hH => hMmax H (by simpa using hH)⟩
      refine ⟨M, Or.inr hM, fun H hH => ?_⟩
      rcases ht.total hH hM with h | h
      · exact h
      · exact (Subgroup.eq_of_le_of_card_ge h (hMmax H hH)).ge
    · exact ⟨⊥, Or.inl rfl, fun H hH => (hne ⟨H, hH⟩).elim⟩
  have key : ∀ m : ℕ, ∀ K : Subgroup G, Nat.card K = p ^ m → ∀ t : Set (Subgroup G),
      IsChain (· ≤ ·) t → (∀ H ∈ t, H ≤ K) →
      ∃ F : ℕ → Subgroup G, (∀ k ≤ m, Nat.card (F k) = p ^ k) ∧
        (∀ a b, a ≤ b → b ≤ m → F a ≤ F b) ∧ (∀ H ∈ t, ∃ k ≤ m, F k = H) ∧ F m = K := by
    intro m
    induction m with
    | zero =>
      intro K hK t ht htK
      refine ⟨fun _ => K, fun k hk => ?_, fun a b _ _ => le_rfl, fun H hH => ⟨0, le_rfl, ?_⟩, rfl⟩
      · obtain rfl : k = 0 := by omega
        exact hK
      · exact (Subgroup.eq_of_le_of_card_ge (htK H hH)
          (by rw [hK, pow_zero]; exact Nat.card_pos)).symm
    | succ m ih =>
      intro K hK t ht htK
      have ht' : ∀ H ∈ t \ {K}, Nat.card H ∣ p ^ m := by
        intro H hH
        have h1 : Nat.card H ∣ p ^ (m + 1) := by
          rw [← hK]
          exact Subgroup.card_dvd_of_le (htK H hH.1)
        obtain ⟨j, hj, hHj⟩ := (Nat.dvd_prime_pow hp).mp h1
        rw [hHj]
        apply pow_dvd_pow
        by_contra hjm
        apply hH.2
        rw [Set.mem_singleton_iff]
        apply Subgroup.eq_of_le_of_card_ge (htK H hH.1)
        rw [hK, hHj]
        exact Nat.pow_le_pow_right hp.pos (by omega)
      obtain ⟨M, hMt, hM⟩ := hmax (t \ {K}) (ht.mono fun x hx => hx.1)
      have hMK : M ≤ K := by
        rcases hMt with h | h
        · rw [h]
          exact bot_le
        · exact htK M h.1
      have hMdvd : Nat.card M ∣ p ^ m := by
        rcases hMt with h | h
        · rw [h, Subgroup.card_bot]
          exact one_dvd _
        · exact ht' M h
      obtain ⟨K', hK'card, hMK', hK'K⟩ := exists_subgroup_card_pow_prime_le_le hp hMdvd
        (by rw [hK]; exact pow_dvd_pow p (Nat.le_succ m)) hMK
      obtain ⟨F, hFcard, hFmono, hFt, hFm⟩ := ih K' hK'card (t \ {K})
        (ht.mono fun x hx => hx.1) (fun H hH => (hM H hH).trans hMK')
      have hFmK : F m ≤ K := by
        rw [hFm]
        exact hK'K
      refine ⟨fun k => if k ≤ m then F k else K, fun k hk => ?_, fun a b hab hb => ?_,
        fun H hH => ?_, ?_⟩
      · show Nat.card (if k ≤ m then F k else K : Subgroup G) = p ^ k
        by_cases hkm : k ≤ m
        · rw [if_pos hkm]
          exact hFcard k hkm
        · rw [if_neg hkm]
          obtain rfl : k = m + 1 := by omega
          exact hK
      · show (if a ≤ m then F a else K) ≤ (if b ≤ m then F b else K)
        by_cases hbm : b ≤ m
        · rw [if_pos hbm, if_pos (hab.trans hbm)]
          exact hFmono a b hab hbm
        · rw [if_neg hbm]
          by_cases ham : a ≤ m
          · rw [if_pos ham]
            exact (hFmono a m ham le_rfl).trans hFmK
          · exact (if_neg ham).trans_le le_rfl
      · show ∃ k ≤ m + 1, (if k ≤ m then F k else K) = H
        by_cases hHK : H = K
        · exact ⟨m + 1, le_rfl, (if_neg (show ¬ (m + 1 ≤ m) by omega)).trans hHK.symm⟩
        · obtain ⟨k, hk, hFk⟩ := hFt H ⟨hH, hHK⟩
          exact ⟨k, hk.trans (Nat.le_succ m), (if_pos hk).trans hFk⟩
      · show (if m + 1 ≤ m then F (m + 1) else K) = K
        exact if_neg (show ¬ (m + 1 ≤ m) by omega)
  obtain ⟨M, hMt, hM⟩ := hmax s hchain
  have hMdvd : Nat.card M ∣ p ^ n := by
    rcases hMt with h | h
    · rw [h, Subgroup.card_bot]
      exact one_dvd _
    · exact hcard M h
  obtain ⟨K, hKcard, hMK, -⟩ := exists_subgroup_card_pow_prime_le_le hp hMdvd
    (by rw [Subgroup.card_top]; exact hdvd) (le_top : M ≤ ⊤)
  obtain ⟨F, hFcard, hFmono, hFs, -⟩ :=
    key n K hKcard s hchain (fun H hH => (hM H hH).trans hMK)
  refine ⟨OrderEmbedding.ofStrictMono (fun k : Fin (n + 1) => F k.val) ?_, ?_, ?_⟩
  · intro a b hab
    show F a.val < F b.val
    have hab' : a.val < b.val := hab
    have ha : a.val ≤ n := Nat.le_of_lt_succ a.isLt
    have hb : b.val ≤ n := Nat.le_of_lt_succ b.isLt
    refine lt_of_le_of_ne (hFmono a.val b.val hab'.le hb) fun h => ?_
    have h1 := hFcard a.val ha
    rw [h, hFcard b.val hb] at h1
    have h2 := Nat.pow_right_injective hp.two_le h1
    omega
  · intro H hH
    obtain ⟨k, hk, hFk⟩ := hFs H hH
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, hFk⟩
  · intro k
    exact hFcard k.val (Nat.le_of_lt_succ k.isLt)
