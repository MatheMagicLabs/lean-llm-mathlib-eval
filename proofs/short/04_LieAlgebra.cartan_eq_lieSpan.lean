/-
Machine-generated proof, verified by Lean.

Theorem:      LieAlgebra.cartan_eq_lieSpan
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/Lie/Basis/Base.lean, line 134
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  6 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), given a hint on proof strategy, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (5.4 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

private lemma cartan_eq_lieSpan [IsKilling K L] (b : (rootSystem H).Base) :
    H = lieSpan K L (range fun i : b.support ↦ (rootSystem H).coroot i) := by
  have hall : Submodule.span K (range ⇑(rootSystem H).coroot) = ⊤ := by
    first
      | exact (rootSystem H).span_coroot_eq_top
      | exact RootPairing.IsRootSystem.span_coroot_eq_top
      | exact RootSystem.span_coroot_eq_top _
      | simp
  have hrange : (range fun i : b.support ↦ (rootSystem H).coroot i) =
      (rootSystem H).coroot '' b.support := by
    ext x
    simp
  have hspan : Submodule.span K (range fun i : b.support ↦ (rootSystem H).coroot i) = ⊤ := by
    first
      | exact b.span_coroot_eq_top
      | rw [hrange, b.span_coroot_support]; exact hall
      | (rw [hrange, b.span_coroot_support]; done)
      | simpa [hrange] using hall
      | rw [hrange, eq_top_iff, ← hall, Submodule.span_le]
        rintro - ⟨j, rfl⟩
        have hcl : ∀ z, z ∈ AddSubmonoid.closure ((rootSystem H).coroot '' b.support) →
            z ∈ Submodule.span K ((rootSystem H).coroot '' b.support) := fun z hz =>
          (AddSubmonoid.closure_le (S := (Submodule.span K
            ((rootSystem H).coroot '' b.support)).toAddSubmonoid)).2
            (Submodule.subset_span (R := K)) hz
        rcases b.coroot_mem_or_neg_mem j with h | h
        · exact hcl _ h
        · simpa using neg_mem (hcl _ h)
  have key : ∀ y : H, (y : L) ∈
      lieSpan K L (range fun i : b.support ↦ ((rootSystem H).coroot i : L)) := by
    intro y
    have hy : y ∈ Submodule.span K (range fun i : b.support ↦ (rootSystem H).coroot i) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact subset_lieSpan (Set.mem_range_self i)
    | zero =>
      first
        | exact zero_mem _
        | simp
    | add z w _ _ hz hw =>
      first
        | exact add_mem hz hw
        | simpa using add_mem hz hw
    | smul a z _ hz =>
      first
        | exact SMulMemClass.smul_mem a hz
        | simpa using SMulMemClass.smul_mem a hz
  refine le_antisymm (fun x hx => key ⟨x, hx⟩) ?_
  rw [LieSubalgebra.lieSpan_le]
  rintro - ⟨i, rfl⟩
  exact ((rootSystem H).coroot i).2
