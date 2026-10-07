/-
Machine-generated proof, verified by Lean.

Theorem:      Convexity.StdSimplex.mem_range_map_iff
Source:       Mathlib @ d0a050ad6, Mathlib/Geometry/Convex/ConvexSpace/Defs.lean, line 220
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  33 tactic steps; area: Geometry
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma mem_range_map_iff
    (f : X → Y) (s : StdSimplex R Y) :
    s ∈ Set.range (map f) ↔ ∀ (x : Y), x ∉ Set.range f → s.weights x = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ x hx
    rw [weights_map]
    exact Finsupp.mapDomain_notin_range _ _ hx
  · intro h
    have : Nonempty X := by
      obtain ⟨y, hy⟩ := s.support_weights_nonempty
      by_contra hX
      apply Finsupp.mem_support_iff.mp hy
      apply h
      rintro ⟨x, -⟩
      exact hX ⟨x⟩
    refine ⟨s.map (Function.invFun f), ?_⟩
    rw [map_map]
    apply StdSimplex.ext
    rw [weights_map, Finsupp.mapDomain_congr (g := id), Finsupp.mapDomain_id]
    intro y hy
    exact Function.invFun_eq (Classical.byContradiction fun hy' =>
      Finsupp.mem_support_iff.mp hy (h y hy'))
