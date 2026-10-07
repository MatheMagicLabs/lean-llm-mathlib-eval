/-
Machine-generated proof, verified by Lean.

Theorem:      Finset.exists_shatters_of_dualFamily_shatters
Source:       Mathlib @ d0a050ad6, Mathlib/Combinatorics/SetFamily/DualVC.lean, line 115
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  27 tactic steps; area: Combinatorics
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.5 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_shatters_of_dualFamily_shatters
    (𝒜 : Finset (Finset α)) (X : Finset α)
    {S : Finset (Finset α)} (hS : (𝒜.dualFamily X).Shatters S)
    {n : ℕ} (hcard : 2 ^ n ≤ #S) :
    ∃ T : Finset α, T ⊆ X ∧ #T = n ∧ 𝒜.Shatters T := by
  have hSA : S ⊆ 𝒜 := subset_of_dualFamily_shatters hS
  have cube : (Fin n → Bool) ↪ ↥S := cubeEmbedding S hcard
  have key : ∀ k : Fin n, ∃ x ∈ X, ∀ b : Fin n → Bool, x ∈ (cube b).val ↔ b k = true := by
    intro k
    obtain ⟨u, hu, hSu⟩ := hS (cubeBitSlice_subset cube k)
    obtain ⟨x, hx, rfl⟩ := mem_dualFamily.mp hu
    refine ⟨x, hx, fun b => ?_⟩
    rw [← mem_cubeBitSlice_iff cube b k, ← hSu, mem_inter, mem_filter]
    have hbS : (cube b).val ∈ S := (cube b).property
    exact ⟨fun hxb => ⟨hbS, hSA hbS, hxb⟩, fun h => h.2.2⟩
  choose x hxX hx using key
  have hinj : Function.Injective x := by
    intro k l hkl
    have h1 := (hx k (fun i => decide (i = k))).mpr (by simp)
    rw [hkl] at h1
    have h2 := (hx l (fun i => decide (i = k))).mp h1
    have h3 : l = k := by simpa using h2
    exact h3.symm
  refine ⟨univ.image x, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨k, -, rfl⟩ := mem_image.mp hy
    exact hxX k
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro t ht
    refine ⟨(cube fun k => decide (x k ∈ t)).val, hSA (cube _).property, ?_⟩
    ext y
    rw [mem_inter]
    constructor
    · rintro ⟨hyT, hyu⟩
      obtain ⟨k, -, rfl⟩ := mem_image.mp hyT
      have h := (hx k _).mp hyu
      simpa using h
    · intro hyt
      refine ⟨ht hyt, ?_⟩
      obtain ⟨k, -, rfl⟩ := mem_image.mp (ht hyt)
      exact (hx k _).mpr (by simpa using hyt)
