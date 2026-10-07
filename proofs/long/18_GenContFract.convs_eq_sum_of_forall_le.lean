/-
Machine-generated proof, verified by Lean.

Theorem:      GenContFract.convs_eq_sum_of_forall_le
Source:       Mathlib @ d0a050ad6, Mathlib/Algebra/ContinuedFractions/Euler.lean, line 303
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  33 tactic steps; area: Algebra
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem convs_eq_sum_of_forall_le (hB : ∀ m ≤ n, g.dens m ≠ 0) :
    g.convs n = g.h + ∑ i ∈ Finset.range n,
      - (∏ j ∈ Finset.range (i + 1), -(g.partNums.get? j).getD 0) /
        (g.dens i * g.dens (i + 1)) := by
  have key : ∀ i ∈ Finset.range n,
      -(∏ j ∈ Finset.range (i + 1), -(g.partNums.get? j).getD 0) /
        (g.dens i * g.dens (i + 1)) = g.convs (i + 1) - g.convs i := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have h1 : g.dens i ≠ 0 := hB i (by omega)
    have h2 : g.dens (i + 1) ≠ 0 := hB (i + 1) (by omega)
    have det := determinant (g := g) (n := i)
    have hP : (∏ j ∈ Finset.range (i + 1), -(g.partNums.get? j).getD 0) =
        g.nums i * g.dens (i + 1) - g.dens i * g.nums (i + 1) := det.symm.trans (by ring)
    rw [hP]
    simp only [convs]
    rw [div_sub_div _ _ h2 h1]
    ring
  have hsum : ∑ i ∈ Finset.range n,
      -(∏ j ∈ Finset.range (i + 1), -(g.partNums.get? j).getD 0) /
        (g.dens i * g.dens (i + 1)) = ∑ i ∈ Finset.range n, (g.convs (i + 1) - g.convs i) :=
    Finset.sum_congr rfl key
  have h0 : g.convs 0 = g.h := by simp [convs, zeroth_num_eq_h, zeroth_den_eq_one]
  rw [hsum, Finset.sum_range_sub g.convs n, h0]
  ring
