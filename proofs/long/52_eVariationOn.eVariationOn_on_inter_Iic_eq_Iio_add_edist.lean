/-
Machine-generated proof, verified by Lean.

Theorem:      eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/EMetricSpace/BoundedVariation.lean, line 601
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  44 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.1 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem eVariationOn_on_inter_Iic_eq_Iio_add_edist
    [TopologicalSpace α] [OrderTopology α] {f : α → M} {s : Set α} {a : α} {l : M}
    (h : (𝓝[s ∩ Iio a] a).NeBot) (ha : a ∈ s)
    (h'f : Tendsto f (𝓝[s ∩ Iio a] a) (𝓝 l)) :
    eVariationOn f (s ∩ Iic a) = eVariationOn f (s ∩ Iio a) + edist (f a) l := by
  apply le_antisymm
  · refine iSup_le fun ⟨n, ⟨u, hu, us⟩⟩ ↦ ?_
    show ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
      eVariationOn f (s ∩ Iio a) + edist (f a) l
    induction n with
    | zero => simp
    | succ m ih =>
      have h1 : u (m + 1) ≤ a := (us (m + 1)).2
      rcases lt_or_eq_of_le h1 with hlt | he
      · have h2 : ∑ i ∈ Finset.Ico 0 (m + 1), edist (f (u (i + 1))) (f (u i)) ≤
            eVariationOn f (s ∩ Iio a) :=
          sum_le_of_monotoneOn_Icc (hu.monotoneOn _)
            fun i hi => ⟨(us i).1, lt_of_le_of_lt (hu hi.2) hlt⟩
        rw [← Finset.range_eq_Ico] at h2
        exact h2.trans le_self_add
      · rw [Finset.sum_range_succ, he]
        have h2 : u m ≤ a := (us m).2
        rcases lt_or_eq_of_le h2 with hlt' | he'
        · have key : ∀ b ∈ s ∩ Iio a, u m < b →
              ∑ i ∈ Finset.range m, edist (f (u (i + 1))) (f (u i)) + edist (f b) (f (u m)) ≤
                eVariationOn f (s ∩ Iio a) := by
            intro b hb hub
            have hw : Monotone (fun i => if i ≤ m then u i else b) := by
              intro i j hij
              show (if i ≤ m then u i else b) ≤ (if j ≤ m then u j else b)
              split_ifs
              all_goals
                first
                | exact hu hij
                | exact (hu ‹i ≤ m›).trans (le_of_lt hub)
                | exact absurd (le_trans hij ‹j ≤ m›) ‹¬i ≤ m›
                | exact le_rfl
            have hws : ∀ i, (fun i => if i ≤ m then u i else b) i ∈ s ∩ Iio a := by
              intro i
              show (if i ≤ m then u i else b) ∈ s ∩ Iio a
              split_ifs
              all_goals
                first
                | exact ⟨(us i).1, lt_of_le_of_lt (hu ‹i ≤ m›) hlt'⟩
                | exact hb
            have hsum : ∑ i ∈ Finset.range (m + 1),
                edist (f ((fun i => if i ≤ m then u i else b) (i + 1)))
                  (f ((fun i => if i ≤ m then u i else b) i)) ≤ eVariationOn f (s ∩ Iio a) := by
              first
              | exact sum_le hw hws
              | exact sum_le f (m + 1) hw hws
            refine le_trans (le_of_eq ?_) hsum
            rw [Finset.sum_range_succ]
            congr 1
            · refine Finset.sum_congr rfl fun i hi => ?_
              have hi' : i < m := Finset.mem_range.mp hi
              simp only [if_pos hi'.le, if_pos (show i + 1 ≤ m by omega)]
            · simp only [if_pos (le_refl m), if_neg (show ¬(m + 1 ≤ m) by omega)]
          have hlim : Tendsto (fun b => eVariationOn f (s ∩ Iio a) + edist (f a) l + edist l (f b))
              (𝓝[s ∩ Iio a] a) (𝓝 (eVariationOn f (s ∩ Iio a) + edist (f a) l + 0)) := by
            apply Tendsto.add tendsto_const_nhds
            rw [← edist_self l]
            exact Tendsto.edist tendsto_const_nhds h'f
          have hfin : ∑ i ∈ Finset.range m, edist (f (u (i + 1))) (f (u i)) + edist (f a) (f (u m)) ≤
              eVariationOn f (s ∩ Iio a) + edist (f a) l + 0 := by
            refine ge_of_tendsto hlim ?_
            filter_upwards [self_mem_nhdsWithin,
              mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt')] with b hb hub
            calc ∑ i ∈ Finset.range m, edist (f (u (i + 1))) (f (u i)) + edist (f a) (f (u m))
                ≤ ∑ i ∈ Finset.range m, edist (f (u (i + 1))) (f (u i)) +
                    (edist (f a) l + edist l (f b) + edist (f b) (f (u m))) :=
                  add_le_add le_rfl (edist_triangle4 _ _ _ _)
              _ = (∑ i ∈ Finset.range m, edist (f (u (i + 1))) (f (u i)) + edist (f b) (f (u m))) +
                    (edist (f a) l + edist l (f b)) := by ring
              _ ≤ eVariationOn f (s ∩ Iio a) + (edist (f a) l + edist l (f b)) :=
                  add_le_add (key b hb hub) le_rfl
              _ = eVariationOn f (s ∩ Iio a) + edist (f a) l + edist l (f b) := by ring
          rwa [add_zero] at hfin
        · rw [he', edist_self, add_zero]
          exact ih
  · have hne : (s ∩ Iio a).Nonempty := h.nonempty_of_mem self_mem_nhdsWithin
    haveI : Nonempty { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s ∩ Iio a } :=
      nonempty_monotone_mem hne
    have key2 : ∀ b ∈ s ∩ Iio a,
        eVariationOn f (s ∩ Iic b) + edist (f b) (f a) ≤ eVariationOn f (s ∩ Iic a) := by
      intro b hb
      have hba : b ≤ a := le_of_lt (show b < a from hb.2)
      have hg : IsGreatest (s ∩ Iic b) b := ⟨⟨hb.1, le_rfl⟩, inter_subset_right⟩
      have hl : IsLeast ({a} : Set α) a := isLeast_singleton
      have h0 : eVariationOn f ({a} : Set α) = 0 := by
        apply eVariationOn.subsingleton
        exact Set.subsingleton_singleton
      have e := union' f hg hl hba
      rw [h0, add_zero] at e
      rw [← e]
      apply eVariationOn.mono
      intro y hy
      rcases hy with hy | hy
      · exact ⟨hy.1, le_trans (show y ≤ b from hy.2) hba⟩
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ⟨ha, le_rfl⟩
    show (⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s ∩ Iio a },
      ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) + edist (f a) l ≤ _
    rw [ENNReal.iSup_add]
    refine iSup_le fun ⟨n, ⟨u, hu, us⟩⟩ ↦ ?_
    show ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) + edist (f a) l ≤
      eVariationOn f (s ∩ Iic a)
    have hc : u n ∈ s ∩ Iio a := us n
    have hS : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
        eVariationOn f (s ∩ Iic (u n)) := by
      rw [Finset.range_eq_Ico]
      exact sum_le_of_monotoneOn_Icc (hu.monotoneOn _) fun i hi => ⟨(us i).1, hu hi.2⟩
    have hlim2 : Tendsto (fun b => eVariationOn f (s ∩ Iic (u n)) + edist (f b) (f a))
        (𝓝[s ∩ Iio a] a) (𝓝 (eVariationOn f (s ∩ Iic (u n)) + edist l (f a))) := by
      apply Tendsto.add tendsto_const_nhds
      exact Tendsto.edist h'f tendsto_const_nhds
    have h3 : eVariationOn f (s ∩ Iic (u n)) + edist l (f a) ≤ eVariationOn f (s ∩ Iic a) := by
      refine le_of_tendsto hlim2 ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show u n < a from hc.2))] with b hb hcb
      calc eVariationOn f (s ∩ Iic (u n)) + edist (f b) (f a)
          ≤ eVariationOn f (s ∩ Iic b) + edist (f b) (f a) := by
            refine add_le_add ?_ le_rfl
            apply eVariationOn.mono
            exact inter_subset_inter_right _ (Iic_subset_Iic.mpr (le_of_lt (show u n < b from hcb)))
        _ ≤ eVariationOn f (s ∩ Iic a) := key2 b hb
    calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) + edist (f a) l
        ≤ eVariationOn f (s ∩ Iic (u n)) + edist l (f a) := by
          rw [edist_comm (f a) l]
          exact add_le_add hS le_rfl
      _ ≤ eVariationOn f (s ∩ Iic a) := h3
