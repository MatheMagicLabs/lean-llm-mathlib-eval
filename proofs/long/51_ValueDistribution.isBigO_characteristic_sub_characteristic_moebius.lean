/-
Machine-generated proof, verified by Lean.

Theorem:      ValueDistribution.isBigO_characteristic_sub_characteristic_moebius
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Complex/ValueDistribution/FirstMainTheorem.lean, line 202
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  46 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem isBigO_characteristic_sub_characteristic_moebius {a b c d : ℂ} {f : ℂ → ℂ}
    (hf : Meromorphic f) (hΔ : a * d - b * c ≠ 0) :
    (characteristic f ⊤ - characteristic ((a * f · + b) / (c * f · + d)) ⊤)
      =O[atTop] (1 : ℝ → ℝ) := by
  show (characteristic f ⊤ - characteristic (fun z ↦ (a * f z + b) / (c * f z + d)) ⊤)
    =O[atTop] (1 : ℝ → ℝ)
  have htrans : ∀ g₁ g₂ g₃ : ℂ → ℂ,
      (characteristic g₁ ⊤ - characteristic g₂ ⊤) =O[atTop] (1 : ℝ → ℝ) →
      (characteristic g₂ ⊤ - characteristic g₃ ⊤) =O[atTop] (1 : ℝ → ℝ) →
      (characteristic g₁ ⊤ - characteristic g₃ ⊤) =O[atTop] (1 : ℝ → ℝ) :=
    fun g₁ g₂ g₃ h₁ h₂ ↦ transitivity₁ g₂ h₂ h₁
  have hsymm : ∀ g₁ g₂ : ℂ → ℂ,
      (characteristic g₁ ⊤ - characteristic g₂ ⊤) =O[atTop] (1 : ℝ → ℝ) →
      (characteristic g₂ ⊤ - characteristic g₁ ⊤) =O[atTop] (1 : ℝ → ℝ) := by
    intro g₁ g₂ h
    rw [← neg_sub]
    exact h.neg_left
  have hshift : ∀ g : ℂ → ℂ, Meromorphic g → ∀ s : ℂ,
      (characteristic g ⊤ - characteristic (fun z ↦ g z + s) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
    intro g hg s
    refine transitivity₂ ?_ (isBigO_characteristic_sub_characteristic_shift (a₀ := -s) hg)
    filter_upwards with z
    simp
  have hinv : ∀ g : ℂ → ℂ, Meromorphic g →
      (characteristic g ⊤ - characteristic (fun z ↦ (g z)⁻¹) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
    fun g hg ↦ isBigO_characteristic_sub_characteristic_inv hg
  have hconstT : ∀ g : ℂ → ℂ, Meromorphic g → ∀ k : ℂ, (∀ᶠ z in codiscrete ℂ, g z = k) →
      (characteristic g ⊤ - characteristic (fun _ : ℂ ↦ (0 : ℂ)) ⊤) =O[atTop] (1 : ℝ → ℝ) := by
    intro g hg k hk
    refine transitivity₂ ?_ (hshift g hg (-k))
    filter_upwards [hk] with z hz
    simp [hz]
  have hcod : ∀ {P : ℂ → Prop}, (∀ x : ℂ, ∀ᶠ z in nhdsWithin x {x}ᶜ, P z) →
      ∀ᶠ z in codiscrete ℂ, P z := by
    intro P h
    first
      | rw [Filter.Eventually, mem_codiscrete]
        intro x
        rw [Filter.disjoint_principal_right, compl_compl]
        exact h x
      | simp only [Filter.codiscrete, Filter.codiscreteWithin, Filter.eventually_iSup]
        intro x _
        rw [← Set.compl_eq_univ_diff]
        exact h x
      | rw [Filter.Eventually, mem_codiscreteWithin]
        intro x _
        rw [Filter.disjoint_principal_right, ← Set.compl_eq_univ_diff, compl_compl]
        exact h x
  have hdich : ∀ g : ℂ → ℂ, Meromorphic g →
      (∀ x : ℂ, ∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0) ∨
        (∀ x : ℂ, ∀ᶠ z in nhdsWithin x {x}ᶜ, g z ≠ 0) := by
    intro g hg
    have hat : ∀ x : ℂ, MeromorphicAt g x := by
      intro x
      first
        | exact hg x
        | exact hg.meromorphicOn x (Set.mem_univ x)
        | exact hg.meromorphicAt
    have hloc : ∀ x : ℂ, (∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0) ∨
        (∀ᶠ z in nhdsWithin x {x}ᶜ, g z ≠ 0) := by
      intro x
      first
        | exact (hat x).eventually_eq_zero_or_eventually_ne_zero
        | by_cases h : meromorphicOrderAt g x = ⊤
          · left
            first
              | exact meromorphicOrderAt_eq_top_iff.1 h
              | exact (meromorphicOrderAt_eq_top_iff (hat x)).1 h
          · right
            first
              | exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hat x)).1 h
              | exact meromorphicOrderAt_ne_top_iff_eventually_ne_zero.1 h
    have hopen : IsOpen {x : ℂ | ∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      have hx0 : ∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0 := hx
      have H : ∀ᶠ z in nhds x, z ∈ ({x}ᶜ : Set ℂ) → g z = 0 := eventually_nhdsWithin_iff.1 hx0
      filter_upwards [H.eventually_nhds] with y hy
      by_cases hyx : y = x
      · rw [hyx]
        exact hx
      · show ∀ᶠ z in nhdsWithin y {y}ᶜ, g z = 0
        apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        filter_upwards [hy, isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hyx)]
          with z hz hzx
        exact hz hzx
    have hclosed : IsClosed {x : ℂ | ∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0} := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      have hx0 : ¬ (∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0) := hx
      have hx' : ∀ᶠ z in nhdsWithin x {x}ᶜ, g z ≠ 0 := (hloc x).resolve_left hx0
      have H : ∀ᶠ z in nhds x, z ∈ ({x}ᶜ : Set ℂ) → g z ≠ 0 := eventually_nhdsWithin_iff.1 hx'
      filter_upwards [H.eventually_nhds] with y hy
      by_cases hyx : y = x
      · rw [hyx]
        exact hx
      · show ¬ (∀ᶠ z in nhdsWithin y {y}ᶜ, g z = 0)
        intro hyA
        have h1 : ∀ᶠ z in nhdsWithin y {y}ᶜ, g z ≠ 0 := by
          apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
          filter_upwards [hy, isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hyx)]
            with z hz hzx
          exact hz hzx
        obtain ⟨z, hz1, hz2⟩ := (h1.and hyA).exists
        exact hz1 hz2
    by_cases hne : ∃ x₀ : ℂ, ∀ᶠ z in nhdsWithin x₀ {x₀}ᶜ, g z = 0
    · left
      obtain ⟨x₀, hx₀⟩ := hne
      have hcl : IsClopen {x : ℂ | ∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0} := by
        first
          | exact ⟨hclosed, hopen⟩
          | exact ⟨hopen, hclosed⟩
      have huniv := hcl.eq_univ ⟨x₀, hx₀⟩
      intro x
      have hx : x ∈ {x : ℂ | ∀ᶠ z in nhdsWithin x {x}ᶜ, g z = 0} := by
        rw [huniv]
        exact Set.mem_univ x
      exact hx
    · right
      intro x
      exact (hloc x).resolve_left (fun h ↦ hne ⟨x, h⟩)
  have key : ∀ (g : ℂ → ℂ) (a b c d : ℂ), Meromorphic g →
      (∀ v : ℂ, ∀ᶠ z in codiscrete ℂ, g z ≠ v) → c ≠ 0 → a * d - b * c ≠ 0 →
      (characteristic g ⊤ - characteristic (fun z ↦ (a * g z + b) / (c * g z + d)) ⊤)
        =O[atTop] (1 : ℝ → ℝ) := by
    intro g a b c d hg hnc hc hΔ
    obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, μ ^ 2 = a * d - b * c := by
      first
        | exact IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
        | exact Complex.exists_pow_nat_eq _ (by norm_num)
        | exact ⟨_, Complex.cpow_nat_inv_pow _ two_ne_zero⟩
    have hμ0 : μ ≠ 0 := by
      intro h
      apply hΔ
      rw [← hμ, h, zero_pow two_ne_zero]
    obtain ⟨C, hC⟩ : ∃ C : ℂ, μ * C = c :=
      ⟨μ⁻¹ * c, by rw [← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℂ, c * Y = d - μ :=
      ⟨c⁻¹ * (d - μ), by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
    obtain ⟨X, hX⟩ : ∃ X : ℂ, c * X = a - μ :=
      ⟨c⁻¹ * (a - μ), by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
    have hXY : X * d + μ * Y = b := by
      have h : c * (X * d + μ * Y - b) = 0 := by
        linear_combination d * hX + μ * hY - hμ
      have h' := (mul_eq_zero.1 h).resolve_left hc
      linear_combination h'
    have s1 := hshift g hg Y
    have s2 := hinv (fun z ↦ g z + Y) (by fun_prop)
    have s3 := hshift (fun z ↦ (g z + Y)⁻¹) (by fun_prop) C
    have s4 := hinv (fun z ↦ (g z + Y)⁻¹ + C) (by fun_prop)
    have s5 := hshift (fun z ↦ ((g z + Y)⁻¹ + C)⁻¹) (by fun_prop) X
    refine transitivity₂ ?_
      (htrans _ _ _ s1 (htrans _ _ _ s2 (htrans _ _ _ s3 (htrans _ _ _ s4 s5))))
    filter_upwards [hnc (-Y), hnc (-d / c)] with z hz1 hz2
    have hw : g z + Y ≠ 0 := by
      intro h
      apply hz1
      linear_combination h
    have hden : c * g z + d ≠ 0 := by
      intro h
      apply hz2
      rw [eq_div_iff hc]
      linear_combination h
    have key1 : ((g z + Y)⁻¹ + C) * (μ * (g z + Y)) = c * g z + d := by
      have hi : (g z + Y)⁻¹ * (g z + Y) = 1 := inv_mul_cancel₀ hw
      linear_combination μ * hi + (g z + Y) * hC + hY
    have hne : (g z + Y)⁻¹ + C ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at key1
      exact hden key1.symm
    have key2 : ((g z + Y)⁻¹ + C)⁻¹ * (c * g z + d) = μ * (g z + Y) := by
      rw [← key1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    show ((g z + Y)⁻¹ + C)⁻¹ + X = (a * g z + b) / (c * g z + d)
    rw [eq_div_iff hden, add_mul, key2]
    linear_combination g z * hX + hXY
  have hM : Meromorphic (fun z ↦ (a * f z + b) / (c * f z + d)) := by fun_prop
  by_cases hconst : ∃ k : ℂ, ∀ᶠ z in codiscrete ℂ, f z = k
  · obtain ⟨k, hk⟩ := hconst
    have hk' : ∀ᶠ z in codiscrete ℂ,
        (a * f z + b) / (c * f z + d) = (a * k + b) / (c * k + d) := by
      filter_upwards [hk] with z hz
      rw [hz]
    exact htrans _ _ _ (hconstT f hf k hk) (hsymm _ _ (hconstT _ hM _ hk'))
  · have hnc : ∀ v : ℂ, ∀ᶠ z in codiscrete ℂ, f z ≠ v := by
      intro v
      rcases hdich (fun z ↦ f z - v) (by fun_prop) with h | h
      · refine (hconst ⟨v, ?_⟩).elim
        filter_upwards [hcod h] with z hz
        linear_combination hz
      · filter_upwards [hcod h] with z hz h'
        exact hz (by rw [h', sub_self])
    by_cases hc : c = 0
    · subst hc
      have hd : d ≠ 0 := by
        rintro rfl
        apply hΔ
        ring
      have hnc' : ∀ v : ℂ, ∀ᶠ z in codiscrete ℂ, (f z)⁻¹ ≠ v := by
        intro v
        filter_upwards [hnc v⁻¹] with z hz h
        apply hz
        rw [← h, inv_inv]
      have hΔ' : b * 0 - a * d ≠ 0 := by
        intro h
        apply hΔ
        linear_combination -h
      have hfi : Meromorphic (fun z ↦ (f z)⁻¹) := by fun_prop
      have hk := key (fun z ↦ (f z)⁻¹) b a d 0 hfi hnc' hd hΔ'
      refine transitivity₂ ?_ (htrans _ _ _ (hinv f hf) hk)
      filter_upwards [hnc 0] with z hz
      have h1 : d * (f z)⁻¹ + 0 ≠ 0 := by
        rw [add_zero]
        exact mul_ne_zero hd (inv_ne_zero hz)
      have h2 : 0 * f z + d ≠ 0 := by
        rw [zero_mul, zero_add]
        exact hd
      show (b * (f z)⁻¹ + a) / (d * (f z)⁻¹ + 0) = (a * f z + b) / (0 * f z + d)
      rw [div_eq_div_iff h1 h2]
      linear_combination (-(a * d)) * (mul_inv_cancel₀ hz)
    · exact key f a b c d hf hnc hc hΔ
