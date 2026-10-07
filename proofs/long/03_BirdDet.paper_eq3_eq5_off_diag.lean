/-
Machine-generated proof, verified by Lean.

Theorem:      BirdDet.paper_eq3_eq5_off_diag
Source:       Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean, line 235
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  26 tactic steps; area: LinearAlgebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.0 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem paper_eq3_eq5_off_diag (i j : Fin n) :
    ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j =
      ∑ α' ∈ S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  have hrange : ∀ (α : Fin (p + 1) → Fin n) (t : Fin (p + 1)),
      Set.range α = insert (α t) (Set.range (t.removeNth α)) := by
    intro α t
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Fin.removeNth]
    constructor
    · rintro ⟨s, rfl⟩
      by_cases hs : s = t
      · exact Or.inl (by rw [hs])
      · obtain ⟨z, hz⟩ : ∃ z, t.succAbove z = s := by
          first
            | exact Fin.exists_succAbove_eq hs
            | exact Fin.exists_succAbove_eq_iff.mpr hs
        exact Or.inr ⟨z, by rw [hz]⟩
    · rintro (rfl | ⟨z, rfl⟩)
      · exact ⟨t, rfl⟩
      · exact ⟨_, rfl⟩
  rw [← Finset.sum_product', ← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.1 x.2, x.2.removeNth x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨α', t⟩ h _
    simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_S_iff] at h
    have hα := Fin.strictMono_cons.mp h
    simp only [Finset.mem_product, Finset.mem_Ioi, mem_S_iff]
    exact ⟨hα.1 t, Fin.strictMono_cons.mpr ⟨fun j => hα.1 (t.succAbove j),
      hα.2.comp (Fin.strictMono_succAbove t)⟩⟩
  · rintro ⟨α₁, t₁⟩ h₁ _ ⟨α₂, t₂⟩ h₂ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hk, hβ⟩ := heq
    simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_S_iff] at h₁ h₂
    have hs₁ := (Fin.strictMono_cons.mp h₁).2
    have hs₂ := (Fin.strictMono_cons.mp h₂).2
    have hr : Set.range α₁ = Set.range α₂ := by
      rw [hrange α₁ t₁, hrange α₂ t₂, hk, hβ]
    have hα : α₁ = α₂ := by
      first
        | exact (hs₁.range_inj hs₂).mp hr
        | exact Fin.strictMono_unique hs₁ hs₂ hr
        | exact (StrictMono.range_inj hs₁ hs₂).mp hr
    subst hα
    rw [hs₁.injective hk]
  · rintro ⟨k, β⟩ hb hne
    simp only [Finset.mem_product, Finset.mem_Ioi] at hb
    have hkβ : k ∉ Set.range β := by
      intro hmem
      apply hne
      show bminor A i k β * A k j = 0
      rw [bminor_eq_zero_of_mem_range A β i hmem, zero_mul]
    obtain ⟨t, ht⟩ := exists_insertNth_mem_S hb.2 hb.1 hkβ
    refine ⟨(t.insertNth k β, t), Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, ?_, ?_⟩
    · simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
      exact hne
    · simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  · intros
    rfl
