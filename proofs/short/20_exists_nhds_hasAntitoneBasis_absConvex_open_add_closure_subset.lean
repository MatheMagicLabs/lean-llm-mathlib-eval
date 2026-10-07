/-
Machine-generated proof, verified by Lean.

Theorem:      exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/LocallyConvex/AbsConvex.lean, line 283
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  20 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.3 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset [FirstCountableTopology E] :
    ∃ x : ℕ → Set E, (𝓝 (0 : E)).HasAntitoneBasis x ∧
      ∀ n, IsOpen (x n) ∧ AbsConvex 𝕜 (x n) ∧ x (n + 1) + x (n + 1) ⊆ x n ∧
        closure (x (n + 1)) ⊆ x n := by
  obtain ⟨u, hu, hub⟩ := (nhds_hasBasis_absConvex_open 𝕜 E).exists_antitone_subbasis
  have key : ∀ m, ∀ᶠ n in Filter.atTop, u n + u n ⊆ u m ∧ closure (u n) ⊆ u m := by
    intro m
    have hum : u m ∈ 𝓝 (0 : E) := (hu m).2.1.mem_nhds (hu m).1
    obtain ⟨V, hV, hVm⟩ : ∃ V ∈ 𝓝 (0 : E), ∀ v ∈ V, ∀ w ∈ V, v + w ∈ u m := by
      first
        | exact exists_nhds_zero_half hum
        | (obtain ⟨V, hVo, hV0, hVm⟩ := exists_open_nhds_zero_half hum
           exact ⟨V, hVo.mem_nhds hV0, hVm⟩)
    obtain ⟨C, ⟨hC, hCc⟩, hCm⟩ := (closed_nhds_basis (0 : E)).mem_iff.1 hum
    obtain ⟨k, -, hk⟩ := hub.toHasBasis.mem_iff.1 (Filter.inter_mem hV hC)
    filter_upwards [Filter.eventually_ge_atTop k] with n hkn
    have hn : u n ⊆ V ∩ C := fun y hy => hk (hub.antitone hkn hy)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hVm a (hn ha).1 b (hn hb).1
    · exact (closure_minimal (fun y hy => (hn hy).2) hCc).trans hCm
  obtain ⟨φ, -, hφr, hφb⟩ := hub.subbasis_with_rel key
  have hstep : ∀ n, u (φ (n + 1)) + u (φ (n + 1)) ⊆ u (φ n) ∧
      closure (u (φ (n + 1))) ⊆ u (φ n) := by
    intro n
    first
      | exact hφr (lt_add_one n)
      | exact hφr n (n + 1) (lt_add_one n)
      | (apply hφr; omega)
  exact ⟨fun n => u (φ n), hφb, fun n => ⟨(hu (φ n)).2.1, (hu (φ n)).2.2,
    (hstep n).1, (hstep n).2⟩⟩
