/-
Machine-generated proof, verified by Lean.

Theorem:      DihedralGroup.center_eq_closure_of_even_ne_two
Source:       Mathlib @ d0a050ad6, Mathlib/GroupTheory/SpecificGroups/Dihedral.lean, line 317
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  27 tactic steps; area: GroupTheory
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem center_eq_closure_of_even_ne_two (heven : Even n) (hn2 : n ≠ 2) :
    Subgroup.center (DihedralGroup n) = Subgroup.zpowers (r (n / 2 : ℕ)) := by
  obtain ⟨m, rfl⟩ := heven
  have hdiv : (m + m) / 2 = m := by omega
  rw [hdiv]
  have hmm : (m : ZMod (m + m)) + m = 0 := by
    rw [← Nat.cast_add]
    first
      | exact ZMod.natCast_self (m + m)
      | simp
  have hne2 : (2 : ZMod (m + m)) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod (m + m)) = 0 := by
      first
        | exact_mod_cast h
        | (rw [Nat.cast_ofNat]; exact h)
    have h2' : m + m ∣ 2 := by
      first
        | exact (CharP.cast_eq_zero_iff (ZMod (m + m)) (m + m) 2).mp h2
        | exact (ZMod.natCast_eq_zero_iff_dvd 2 (m + m)).mp h2
        | exact (ZMod.natCast_zmod_eq_zero_iff_dvd 2 (m + m)).mp h2
    have h3 : m + m ≤ 2 := Nat.le_of_dvd (by omega) h2'
    have h4 : m = 0 := by omega
    subst h4
    first
      | simp at h2'
      | (rcases h2' with ⟨c, hc⟩; omega)
  ext x
  rw [Subgroup.mem_center_iff, Subgroup.mem_zpowers_iff]
  rcases x with i | i
  · constructor
    · intro h
      have h1 := h (sr 0)
      rw [sr_mul_r, r_mul_sr] at h1
      have h2 := sr.inj h1
      have hii : i + i = 0 := by
        have h3 : i + i = (0 + i) - (0 - i) := by ring
        rw [h3, h2, sub_self]
      obtain ⟨j, rfl⟩ : ∃ j : ℤ, (j : ZMod (m + m)) = i := by
        first
          | exact ZMod.intCast_surjective i
          | exact ⟨_, ZMod.intCast_zmod_cast i⟩
      have h3 : ((j + j : ℤ) : ZMod (m + m)) = 0 := by
        push_cast
        exact hii
      have h4 : ((m + m : ℕ) : ℤ) ∣ j + j := by
        first
          | exact (CharP.intCast_eq_zero_iff (ZMod (m + m)) (m + m) (j + j)).mp h3
          | exact (ZMod.intCast_zmod_eq_zero_iff_dvd (j + j) (m + m)).mp h3
      obtain ⟨c, hc⟩ := h4
      have hj : j = (m : ℤ) * c := by
        have h5 : (2 : ℤ) * j = 2 * ((m : ℤ) * c) := by
          rw [two_mul, two_mul, hc, Nat.cast_add]
          ring
        first
          | exact mul_left_cancel₀ two_ne_zero h5
          | exact mul_left_cancel₀ (by norm_num) h5
          | omega
      refine ⟨c, ?_⟩
      first
        | (rw [r_zpow, hj, Int.cast_mul, Int.cast_natCast])
        | simp [hj]
    · rintro ⟨k, hk⟩
      rw [r_zpow] at hk
      have hk' := r.inj hk
      have hii : i + i = 0 := by
        rw [← hk', ← add_mul, hmm, zero_mul]
      rintro (j | j)
      · first
          | rw [r_mul_r, r_mul_r, add_comm j i]
          | simp only [r_mul_r, add_comm]
      · rw [sr_mul_r, r_mul_sr]
        have h3 : j + i = j - i := by
          have h4 : j - i = j + i - (i + i) := by ring
          rw [h4, hii, sub_zero]
        rw [h3]
  · constructor
    · intro h
      have h1 := h (r 1)
      rw [r_mul_sr, sr_mul_r] at h1
      have h2 := sr.inj h1
      have h3 : (2 : ZMod (m + m)) = (i + 1) - (i - 1) := by ring
      rw [h2, sub_self] at h3
      exact absurd h3 hne2
    · rintro ⟨k, hk⟩
      rw [r_zpow] at hk
      first
        | cases hk
        | exact DihedralGroup.noConfusion hk
        | simp at hk
