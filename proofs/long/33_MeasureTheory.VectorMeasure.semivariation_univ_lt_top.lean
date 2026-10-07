/-
Machine-generated proof, verified by Lean.

Theorem:      MeasureTheory.VectorMeasure.semivariation_univ_lt_top
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/Variation/Semivariation.lean, line 133
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  25 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), given an outline of the human proof, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma semivariation_univ_lt_top : μ.semivariation univ < ∞ := by
  apply lt_top_iff_ne_top.2
  intro H
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semivariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ :=
    exists_one_le_enorm_apply_of_semivariation_eq_top hs h's
  choose! T hT using A
  let s : ℕ → Set X := fun n ↦ T^[n] univ
  have e (n : ℕ) : s (n + 1) = T (s n) := Function.iterate_succ_apply' T n univ
  have hs (n : ℕ) : MeasurableSet (s n) ∧ μ.semivariation (s n) = ∞ := by
    induction n with
    | zero => exact ⟨MeasurableSet.univ, H⟩
    | succ n ih =>
      have h := hT _ ih.1 ih.2
      rw [e n]
      exact ⟨h.1, h.2.2.1⟩
  let u : ℕ → Set X := fun n ↦ s n \ s (n + 1)
  have hu (n : ℕ) : 1 ≤ ‖μ (u n)‖ₑ := by
    show 1 ≤ ‖μ (s n \ s (n + 1))‖ₑ
    rw [e n]
    exact (hT _ (hs n).1 (hs n).2).2.2.2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le
    intro n
    exact (e n).trans_le (hT _ (hs n).1 (hs n).2).2.1
  have u_disj : Pairwise (Disjoint on u) := by
    have key : ∀ i j, i < j → Disjoint (u i) (u j) := by
      intro i j h
      show Disjoint (s i \ s (i + 1)) (s j \ s (j + 1))
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx.2 (s_anti (Nat.succ_le_of_lt h) hx'.1)
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact key i j h
    · exact absurd h hij
    · exact (key j i h).symm
  have hsum : HasSum (fun i ↦ μ (u i)) (μ (⋃ i, u i)) :=
    μ.m_iUnion' (fun i ↦ (hs i).1.diff (hs (i + 1)).1) u_disj
  have T0 : Tendsto (fun n ↦ ‖μ (u n)‖ₑ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n ↦ μ (u n)) atTop (𝓝 0) := by
      first
      | exact hsum.summable.tendsto_atTop_zero
      | simpa [Nat.cofinite_eq_atTop] using hsum.summable.tendsto_cofinite_zero
    first
    | (have h1 := (continuous_enorm.tendsto (0 : E)).comp h0; rw [enorm_zero] at h1; exact h1)
    | simpa using (continuous_enorm.tendsto (0 : E)).comp h0
    | simpa using h0.enorm
  have hlt : ∀ᶠ x in 𝓝 (0 : ℝ≥0∞), x < 1 := Iio_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1)
  obtain ⟨n, hn⟩ : ∃ n, ‖μ (u n)‖ₑ < 1 := (T0.eventually hlt).exists
  exact lt_irrefl _ (hn.trans_le (hu n))
