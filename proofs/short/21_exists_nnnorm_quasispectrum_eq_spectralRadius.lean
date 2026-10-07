/-
Machine-generated proof, verified by Lean.

Theorem:      exists_nnnorm_quasispectrum_eq_spectralRadius
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Normed/Algebra/Spectrum.lean, line 497
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem exists_nnnorm_quasispectrum_eq_spectralRadius [ProperSpace 𝕜] (a : A) :
    ∃ k ∈ quasispectrum 𝕜 a, (‖k‖₊ : ℝ≥0∞) = spectralRadius 𝕜 a := by
  have hc : IsCompact (quasispectrum 𝕜 a) := quasispectrum.isCompact a
  have hne : (quasispectrum 𝕜 a).Nonempty := by
    first
    | exact ⟨0, quasispectrum.zero_mem ..⟩
    | exact quasispectrum.nonempty ..
    | exact ⟨0, by simp⟩
  obtain ⟨k, hk, h⟩ := hc.exists_isMaxOn hne continuous_nnnorm.continuousOn
  refine ⟨k, hk, le_antisymm ?_ ?_⟩
  · first
    | exact le_iSup₂ (α := ℝ≥0∞) k hk
    | exact le_iSup₂ (α := ℝ≥0∞) (f := fun x (_ : x ∈ quasispectrum 𝕜 a) => (‖x‖₊ : ℝ≥0∞)) k hk
  · first
    | exact iSup₂_le <| mod_cast h
    | exact iSup₂_le fun x hx => ENNReal.coe_le_coe.mpr (isMaxOn_iff.mp h x hx)
