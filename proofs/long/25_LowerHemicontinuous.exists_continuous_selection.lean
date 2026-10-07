/-
Machine-generated proof, verified by Lean.

Theorem:      LowerHemicontinuous.exists_continuous_selection
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/Semicontinuity/Michael.lean, line 107
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  35 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 2;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  have hT : ∀ s ∈ 𝓝 (0 : β), ∃ t : Set β, IsOpen t ∧ Convex ℝ t ∧ (0 : β) ∈ t ∧ t = -t ∧
      ∀ a ∈ t, ∀ b ∈ t, a + b ∈ s := by
    intro s hs
    obtain ⟨W, hW, hWs⟩ := exists_nhds_zero_half hs
    have hK : ∃ K : Set β, (0 : β) ∈ K ∧ IsOpen K ∧ Convex ℝ K ∧ K ⊆ W := by
      first
        | exact ((LocallyConvexSpace.convex_open_basis_zero ℝ β).mem_iff.mp hW).imp
            fun K hK => ⟨hK.1.1, hK.1.2.1, hK.1.2.2, hK.2⟩
        | exact ((LocallyConvexSpace.convex_basis_zero ℝ β).mem_iff.mp hW).elim
            fun S hS => ⟨interior S, mem_interior_iff_mem_nhds.mpr hS.1.1, isOpen_interior,
              hS.1.2.interior, interior_subset.trans hS.2⟩
        | exact ((nhds_hasBasis_absConvex_open ℝ β).mem_iff.mp hW).imp
            fun K hK => ⟨hK.1.1, hK.1.2.1, hK.1.2.2.2, hK.2⟩
    obtain ⟨K, hK0, hKo, hKc, hKW⟩ := hK
    refine ⟨K ∩ -K, hKo.inter hKo.neg, hKc.inter hKc.neg, ⟨hK0, ?_⟩, ?_, ?_⟩
    · first
        | simpa using hK0
        | (rw [Set.mem_neg, _root_.neg_zero]; exact hK0)
    · first
        | (ext v; simp [and_comm]; done)
        | rw [Set.inter_neg, _root_.neg_neg, Set.inter_comm]
    · intro a ha b hb
      exact hWs a (hKW ha.1) b (hKW hb.1)
  choose! T hTo hTc hTz hTs hTh using hT
  obtain ⟨C, hC⟩ := (𝓝 (0 : β)).exists_antitone_basis
  have hCm : ∀ n, C n ∈ 𝓝 (0 : β) := fun n => hC.toHasBasis.mem_of_mem trivial
  have hCt : ∀ φ : ℕ → β, (∀ n, φ n ∈ C n) → Filter.Tendsto φ Filter.atTop (𝓝 0) := by
    intro φ hφ
    first
      | exact hC.tendsto hφ
      | exact hC.toHasBasis.tendsto_right_iff.mpr fun i _ =>
          Filter.eventually_atTop.mpr ⟨i, fun n hn => hC.antitone hn (hφ n)⟩
  obtain ⟨V, hV0, hVs⟩ : ∃ V : ℕ → Set β, V 0 = T (C 0) ∧
      ∀ n, V (n + 1) = T (C (n + 1) ∩ V n) :=
    ⟨fun n => Nat.rec (motive := fun _ => Set β) (T (C 0)) (fun k Vk => T (C (k + 1) ∩ Vk)) n,
      rfl, fun n => rfl⟩
  have hVn : ∀ n, V n ∈ 𝓝 (0 : β) := by
    intro n
    induction n with
    | zero =>
      rw [hV0]
      exact (hTo (C 0) (hCm 0)).mem_nhds (hTz (C 0) (hCm 0))
    | succ k ih =>
      rw [hVs]
      exact (hTo _ (Filter.inter_mem (hCm (k + 1)) ih)).mem_nhds
        (hTz _ (Filter.inter_mem (hCm (k + 1)) ih))
  have hSn : ∀ n, C (n + 1) ∩ V n ∈ 𝓝 (0 : β) := fun n => Filter.inter_mem (hCm (n + 1)) (hVn n)
  have hVo : ∀ n, IsOpen (V n) := by
    intro n
    cases n with
    | zero => rw [hV0]; exact hTo _ (hCm 0)
    | succ k => rw [hVs]; exact hTo _ (hSn k)
  have hVc : ∀ n, Convex ℝ (V n) := by
    intro n
    cases n with
    | zero => rw [hV0]; exact hTc _ (hCm 0)
    | succ k => rw [hVs]; exact hTc _ (hSn k)
  have hVz : ∀ n, (0 : β) ∈ V n := fun n => mem_of_mem_nhds (hVn n)
  have hVsymm : ∀ n, V n = -V n := by
    intro n
    cases n with
    | zero => rw [hV0]; exact hTs _ (hCm 0)
    | succ k => rw [hVs]; exact hTs _ (hSn k)
  have hVhalf : ∀ n, ∀ a ∈ V (n + 1), ∀ b ∈ V (n + 1), a + b ∈ V n := by
    intro n a ha b hb
    rw [hVs] at ha hb
    exact (hTh _ (hSn n) a ha b hb).2
  have hVC : ∀ n, V n ⊆ C n := by
    intro n a ha
    cases n with
    | zero =>
      rw [hV0] at ha
      have h := hTh _ (hCm 0) a ha 0 (hTz _ (hCm 0))
      rwa [_root_.add_zero] at h
    | succ k =>
      rw [hVs] at ha
      have h := hTh _ (hSn k) a ha 0 (hTz _ (hSn k))
      rw [_root_.add_zero] at h
      exact h.1
  have hneg : ∀ n, ∀ a ∈ V n, -a ∈ V n := by
    intro n a ha
    rw [hVsymm n]
    first
      | exact Set.neg_mem_neg.mpr ha
      | simpa using ha
  have h0 : HasOpenLowerSections (fun x => f x + V 0) :=
    (hf.hasOpenCGraph_of_add_hasOpenCGraph (.const (hVo 0))).hasOpenLowerSections
  obtain ⟨g₀, hg₀c, hg₀⟩ := h0.exists_continuous_selection
    (fun x => (hf_nonempty x).add ⟨0, hVz 0⟩) (fun x => (hf_convex x).add (hVc 0))
  have hstepG : ∀ n (h : {h : α → β // Continuous h ∧ ∀ x, h x ∈ f x + V n}),
      ∃ h' : {h : α → β // Continuous h ∧ ∀ x, h x ∈ f x + V (n + 1)},
        ∀ x, h'.1 x ∈ {h.1 x} + V n := by
    intro n h
    obtain ⟨h', h'c, h'f, h's⟩ := LowerHemicontinuous.exists_continuous_selection_refine hf
      hf_convex h.2.1 (hVo (n + 1)) (hVc (n + 1)) (hVo n) (hVc n) (hVz (n + 1)) (hVsymm n) h.2.2
    exact ⟨⟨h', h'c, h'f⟩, h's⟩
  choose F hF using hstepG
  obtain ⟨G, hG⟩ : ∃ G : (n : ℕ) → {h : α → β // Continuous h ∧ ∀ x, h x ∈ f x + V n},
      ∀ n, G (n + 1) = F n (G n) :=
    ⟨fun n => Nat.rec (motive := fun n => {h : α → β // Continuous h ∧ ∀ x, h x ∈ f x + V n})
      ⟨g₀, hg₀c, hg₀⟩ (fun k Gk => F k Gk) n, fun n => rfl⟩
  obtain ⟨u, huc, huf, hud⟩ : ∃ u : ℕ → α → β, (∀ n, Continuous (u n)) ∧
      (∀ n x, u n x ∈ f x + V n) ∧ ∀ n x, u (n + 1) x - u n x ∈ V n := by
    refine ⟨fun n => (G n).1, fun n => (G n).2.1, fun n => (G n).2.2, fun n x => ?_⟩
    have h : (G (n + 1)).1 x ∈ {(G n).1 x} + V n := by
      rw [hG n]
      exact hF n (G n) x
    obtain ⟨a, ha, b, hb, hab⟩ := h
    rw [Set.mem_singleton_iff] at ha
    subst ha
    show (G (n + 1)).1 x - (G n).1 x ∈ V n
    rw [← hab]
    first
      | (rw [_root_.add_sub_cancel_left]; exact hb)
      | simpa using hb
  have htel : ∀ k n x, u (n + 1 + k) x - u (n + 1) x ∈ V n := by
    intro k
    induction k with
    | zero =>
      intro n x
      rw [_root_.add_zero, _root_.sub_self]
      exact hVz n
    | succ k ih =>
      intro n x
      have e : u (n + 1 + (k + 1)) x - u (n + 1) x =
          (u (n + 1 + 1) x - u (n + 1) x) + (u (n + 1 + 1 + k) x - u (n + 1 + 1) x) := by
        rw [show n + 1 + (k + 1) = n + 1 + 1 + k by omega]
        abel
      rw [e]
      exact hVhalf n _ (hud (n + 1) x) _ (ih (n + 1) x)
  have hfar : ∀ n m x, n + 1 ≤ m → u m x - u (n + 1) x ∈ V n := by
    intro n m x hnm
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    exact htel k n x
  have hUC : UniformCauchySeqOn u Filter.atTop Set.univ := by
    intro w hw
    rw [_root_.uniformity_eq_comap_nhds_zero] at hw
    obtain ⟨s, hs, hsw⟩ := Filter.mem_comap.mp hw
    obtain ⟨N, -, hN⟩ := hC.toHasBasis.mem_iff.mp hs
    have hVN : V N ⊆ s := (hVC N).trans hN
    filter_upwards [Filter.prod_mem_prod (Filter.eventually_ge_atTop (N + 1 + 1))
      (Filter.eventually_ge_atTop (N + 1 + 1))] with m hm x _
    have e : u m.2 x - u m.1 x =
        (u m.2 x - u (N + 1 + 1) x) + -(u m.1 x - u (N + 1 + 1) x) := by abel
    have hmem' : u m.2 x - u m.1 x ∈ V N := by
      rw [e]
      exact hVhalf N _ (hfar (N + 1) m.2 x hm.2) _ (hneg _ _ (hfar (N + 1) m.1 x hm.1))
    refine hsw ?_
    exact hVN hmem'
  have hcs : ∀ x, CauchySeq (fun n => u n x) := by
    intro x
    first
      | exact hUC.cauchy_map (Set.mem_univ x)
      | exact hUC.cauchySeq (Set.mem_univ x)
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcs x)
  have hTU : TendstoUniformlyOn u g Filter.atTop Set.univ :=
    hUC.tendstoUniformlyOn_of_tendsto (fun x _ => hg x)
  have hgc : Continuous g := by
    first
      | exact (tendstoUniformlyOn_univ.mp hTU).continuous (Filter.Frequently.of_forall huc)
      | exact (tendstoUniformlyOn_univ.mp hTU).continuous
          (Filter.Eventually.of_forall huc).frequently
      | exact continuousOn_univ.mp
          (hTU.continuousOn (Filter.Frequently.of_forall fun n => (huc n).continuousOn))
      | exact continuousOn_univ.mp (hTU.continuousOn
          (Filter.Eventually.of_forall fun n => (huc n).continuousOn).frequently)
      | exact (tendstoUniformlyOn_univ.mp hTU).continuous (Filter.Eventually.of_forall huc)
  have hsel : ∀ n x, ∃ y ∈ f x, ∃ v ∈ V n, y + v = u n x := by
    intro n x
    obtain ⟨a, ha, b, hb, hab⟩ := huf n x
    exact ⟨a, ha, b, hb, hab⟩
  choose y hy v hv hyv using hsel
  refine ⟨g, hgc, fun x => ?_⟩
  have hv0 : Filter.Tendsto (fun n => v n x) Filter.atTop (𝓝 0) :=
    hCt _ (fun n => hVC n (hv n x))
  have h := (hg x).sub hv0
  rw [_root_.sub_zero] at h
  have e : (fun n => y n x) = fun n => u n x - v n x :=
    funext fun n => eq_sub_of_add_eq (hyv n x)
  have hlim : Filter.Tendsto (fun n => y n x) Filter.atTop (𝓝 (g x)) := by
    rw [e]
    exact h
  exact (hf_isClosed x).mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hy n x)
