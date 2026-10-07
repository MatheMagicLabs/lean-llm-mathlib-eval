/-
Machine-generated proof, verified by Lean.

Theorem:      MonotoneOn.eventually_le_two_mul'
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Function/BorelGrowth.lean, line 52
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  53 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private theorem MonotoneOn.eventually_le_two_mul' {S : ℝ → ℝ} {a : ℝ}
    (h₁ : MonotoneOn S (Set.Ici a)) (h₂ : 0 < S a) :
    ∀ᶠ r in volume.cofinite ⊓ atTop, S (r + (S r)⁻¹) ≤ 2 * S r := by
  have hpair : ∀ n : ℕ,
      ∀ x ∈ {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹) ∧ 2 ^ n * S a ≤ S r ∧
        S r < 2 ^ (n + 1) * S a},
      ∀ y ∈ {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹) ∧ 2 ^ n * S a ≤ S r ∧
        S r < 2 ^ (n + 1) * S a},
      x ≤ y → y - x ≤ (S a)⁻¹ * (1 / 2) ^ n := by
    intro n x hx y hy hxy
    obtain ⟨hax, hx2, hx3, hx4⟩ := hx
    obtain ⟨hay, hy2, hy3, hy4⟩ := hy
    have hpos : (0 : ℝ) < 2 ^ n * S a := mul_pos (pow_pos two_pos n) h₂
    have hSx : 0 < S x := lt_of_lt_of_le hpos hx3
    have hlt : y < x + (S x)⁻¹ := by
      by_contra hcon
      have hcon' : x + (S x)⁻¹ ≤ y := not_lt.mp hcon
      have hax' : a ≤ x + (S x)⁻¹ := by
        have := inv_pos.mpr hSx
        linarith
      have hmono : S (x + (S x)⁻¹) ≤ S y :=
        h₁ (Set.mem_Ici.mpr hax') (Set.mem_Ici.mpr hay) hcon'
      have h2n : (2 : ℝ) ^ (n + 1) * S a = 2 * (2 ^ n * S a) := by ring
      linarith
    have hinv : (S x)⁻¹ ≤ (2 ^ n * S a)⁻¹ := (inv_le_inv₀ hSx hpos).mpr hx3
    have heq : ((2 : ℝ) ^ n * S a)⁻¹ = (S a)⁻¹ * (1 / 2) ^ n := by
      first
        | (rw [one_div, inv_pow, mul_inv_rev]; done)
        | (rw [one_div, inv_pow, mul_inv, mul_comm]; done)
        | ring1
        | (field_simp; done)
        | (field_simp; ring1)
    linarith
  have hvol : ∀ n : ℕ, volume {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹) ∧ 2 ^ n * S a ≤ S r ∧
      S r < 2 ^ (n + 1) * S a} ≤ ENNReal.ofReal (2 * ((S a)⁻¹ * (1 / 2) ^ n)) := by
    intro n
    have hc : 0 ≤ (S a)⁻¹ * (1 / 2 : ℝ) ^ n :=
      mul_nonneg (inv_nonneg.mpr h₂.le) (pow_nonneg (by norm_num) n)
    rcases Set.eq_empty_or_nonempty {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹) ∧
        2 ^ n * S a ≤ S r ∧ S r < 2 ^ (n + 1) * S a} with h | ⟨x₀, hx₀⟩
    · rw [h]
      simp
    · have hsub : {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹) ∧ 2 ^ n * S a ≤ S r ∧
          S r < 2 ^ (n + 1) * S a} ⊆
          Set.Icc (x₀ - (S a)⁻¹ * (1 / 2) ^ n) (x₀ + (S a)⁻¹ * (1 / 2) ^ n) := by
        intro y hy
        rcases le_total x₀ y with hxy | hxy
        · have := hpair n x₀ hx₀ y hy hxy
          exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
        · have := hpair n y hy x₀ hx₀ hxy
          exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
      refine (measure_mono hsub).trans ?_
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      linarith
  have hcover : {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹)} ⊆
      ⋃ n : ℕ, {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹) ∧ 2 ^ n * S a ≤ S r ∧
        S r < 2 ^ (n + 1) * S a} := by
    intro r hr
    obtain ⟨har, hr2⟩ := hr
    have hSr : S a ≤ S r := h₁ (Set.mem_Ici.mpr (le_refl a)) (Set.mem_Ici.mpr har) har
    have h1 : 1 ≤ S r / S a := by
      first
        | (rw [le_div_iff₀ h₂, one_mul]; exact hSr)
        | exact (one_le_div h₂).mpr hSr
        | exact (one_le_div₀ h₂).mpr hSr
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    have hn1' : 2 ^ n * S a ≤ S r := by
      first
        | rwa [le_div_iff₀ h₂] at hn1
        | rwa [le_div_iff h₂] at hn1
    have hn2' : S r < 2 ^ (n + 1) * S a := by
      first
        | rwa [div_lt_iff₀ h₂] at hn2
        | rwa [div_lt_iff h₂] at hn2
    exact Set.mem_iUnion.mpr ⟨n, har, hr2, hn1', hn2'⟩
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    first
      | exact summable_geometric_two
      | exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsumm : Summable (fun n : ℕ => 2 * ((S a)⁻¹ * (1 / 2 : ℝ) ^ n)) :=
    (hgeom.mul_left (S a)⁻¹).mul_left 2
  have hnn : ∀ n : ℕ, 0 ≤ 2 * ((S a)⁻¹ * (1 / 2 : ℝ) ^ n) := fun n =>
    mul_nonneg zero_le_two (mul_nonneg (inv_nonneg.mpr h₂.le) (pow_nonneg (by norm_num) n))
  have hE : volume {r | a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹)} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hcover) ?_
    refine lt_of_le_of_lt (measure_iUnion_le _) ?_
    have hfinite : ∑' n : ℕ, ENNReal.ofReal (2 * ((S a)⁻¹ * (1 / 2 : ℝ) ^ n)) < ⊤ := by
      first
        | exact (ENNReal.ofReal_tsum_of_nonneg hnn hsumm).symm.trans_lt ENNReal.ofReal_lt_top
        | exact lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mpr hsumm.toNNReal)
    first
      | exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hvol) hfinite
      | exact lt_of_le_of_lt (ENNReal.tsum_mono hvol) hfinite
      | exact lt_of_le_of_lt (tsum_mono ENNReal.summable ENNReal.summable hvol) hfinite
  have h1 : ∀ᶠ r in volume.cofinite, ¬ (a ≤ r ∧ 2 * S r < S (r + (S r)⁻¹)) := by
    first
      | (rw [Measure.eventually_cofinite]; simpa only [not_not] using hE)
      | exact Measure.compl_mem_cofinite.mpr hE
  filter_upwards [h1.filter_mono inf_le_left,
    (Filter.eventually_ge_atTop a).filter_mono inf_le_right] with r hr1 hr2
  push_neg at hr1
  exact hr1 hr2
