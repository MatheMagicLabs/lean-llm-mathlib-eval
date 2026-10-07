/-
Machine-generated proof, verified by Lean.

Theorem:      SSet.isColimitCoconeN.fac
Source:       Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/NonDegenerateSimplicesColimit.lean, line 82
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: AlgebraicTopology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma fac (s : Cocone X.functorN) (x : X.N) :
    x.subcomplex.ι ≫ desc s = s.ι.app x := by
  first
  | (dsimp only [desc]
     rw [← Category.assoc]
     exact Multicofork.IsColimit.fac (multicoequalizerDiagram X).isColimit
       (fun x ↦ s.ι.app x) _ x)
  | (rw [← Category.assoc]
     exact Multicofork.IsColimit.fac (multicoequalizerDiagram X).isColimit
       (fun x ↦ s.ι.app x) _ x)
  | (dsimp only [desc]
     rw [← Category.assoc]
     exact Multicofork.IsColimit.fac _ _ _ x)
  | (dsimp only [desc]
     rw [← Category.assoc]
     exact (multicoequalizerDiagram X).isColimit.fac _ (.right x))
  | (dsimp only [desc]
     rw [← Category.assoc]
     convert Multicofork.IsColimit.fac (multicoequalizerDiagram X).isColimit
       (fun x ↦ s.ι.app x) _ x using 2
     all_goals (ext n a; rfl))
