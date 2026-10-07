/-
Machine-generated proof, verified by Lean.

Theorem:      MeasurableSpace.exists_eq_iUnion_countablyGeneratedAtom
Source:       Mathlib @ d0a050ad6, Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean, line 192
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  33 tactic steps; area: MeasureTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.6 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma exists_eq_iUnion_countablyGeneratedAtom {s : Set α} (hs : MeasurableSet s) :
    ∃ (q : (ℕ → Prop) → Prop), s = ⋃ p, if q p then countablyGeneratedAtom α p else ∅ := by
  have hle : mα ≤ MeasurableSpace.comap (fun x n ↦ x ∈ natGeneratingSequence α n) ⊤ := by
    refine le_trans (generateFrom_natGeneratingSequence α).ge (generateFrom_le ?_)
    rintro _ ⟨n, rfl⟩
    exact ⟨{p | p n}, MeasurableSpace.measurableSet_top, rfl⟩
  obtain ⟨u, -, rfl⟩ := hle s hs
  refine ⟨fun p ↦ p ∈ u, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · intro hx
    refine ⟨fun n ↦ x ∈ natGeneratingSequence α n, ?_⟩
    first
      | (rw [if_pos hx]; exact mem_countablyGeneratedAtom_natGeneratingSequence x)
      | simpa [hx] using mem_countablyGeneratedAtom_natGeneratingSequence x
  · rintro ⟨p, hp⟩
    split_ifs at hp with hpu
    · have hxp : (fun n ↦ x ∈ natGeneratingSequence α n) = p := by
        funext n
        have h := hp
        simp only [countablyGeneratedAtom, Set.mem_iInter] at h
        specialize h n
        split_ifs at h with hn
        · exact propext (iff_of_true h hn)
        · rw [Set.mem_compl_iff] at h
          exact propext (iff_of_false h hn)
      first
        | (rw [hxp]; exact hpu)
        | exact hxp ▸ hpu
        | (convert hpu using 1)
    · simp at hp
