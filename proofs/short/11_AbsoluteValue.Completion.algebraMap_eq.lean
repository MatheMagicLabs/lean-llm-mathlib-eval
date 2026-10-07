/-
Machine-generated proof, verified by Lean.

Theorem:      AbsoluteValue.Completion.algebraMap_eq
Source:       Mathlib @ d0a050ad6, Mathlib/Analysis/Normed/Field/WithAbs.lean, line 142
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  4 tactic steps; area: Analysis
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (4.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem algebraMap_eq : algebraMap v.Completion w.Completion =
    UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
      (WithAbs.isometry_map v w).continuous := by
  have key : ∀ x : K, algebraMap K w.Completion x =
      UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
        (WithAbs.isometry_map v w).continuous (algebraMap K v.Completion x) :=
    fun x ↦ (UniformSpace.Completion.mapRingHom_coe (WithAbs.isometry_map v w).continuous
      (WithAbs.toAbs v x)).symm
  have hc1 : Continuous (algebraMap v.Completion w.Completion) := by
    first
    | exact continuous_algebraMap _ _
    | exact continuous_algebraMap
    | fun_prop
    | exact (continuous_id.smul continuous_const).congr
        fun x => (Algebra.algebraMap_eq_smul_one x).symm
  have hc2 : Continuous (UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
      (WithAbs.isometry_map v w).continuous) :=
    (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)).continuous
  refine RingHom.ext fun x ↦ ?_
  refine UniformSpace.Completion.induction_on x (isClosed_eq hc1 hc2) fun a ↦ ?_
  obtain ⟨k, rfl⟩ : ∃ k : K, WithAbs.toAbs v k = a := ⟨WithAbs.ofAbs a, by first | rfl | simp⟩
  exact (IsScalarTower.algebraMap_apply K v.Completion w.Completion k).symm.trans (key k)
