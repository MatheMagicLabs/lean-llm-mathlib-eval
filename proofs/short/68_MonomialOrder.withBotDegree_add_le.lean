/-
Machine-generated proof, verified by Lean.

Theorem:      MonomialOrder.withBotDegree_add_le
Source:       Mathlib @ d0a050ad6, Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean, line 1090
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: RingTheory
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (3.2 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

lemma withBotDegree_add_le :
    (m.toWithBotSyn <| m.withBotDegree (f + g)) ≤
      (m.toWithBotSyn <| m.withBotDegree f) ⊔ (m.toWithBotSyn <| m.withBotDegree g) := by
  by_cases hf : f = 0
  · first
    | simp [hf]
    | simp [hf, toWithBotSyn_apply]
  by_cases hg : g = 0
  · first
    | simp [hg]
    | simp [hg, toWithBotSyn_apply]
  by_cases hfg : f + g = 0
  · first
    | simp [hfg]
    | simp [hfg, toWithBotSyn_apply]
  have key : m.toSyn (m.degree (f + g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
    first
    | exact m.degree_add_le
    | exact m.degree_add_le f g
    | exact degree_add_le
  rw [(m.withBotDegree_eq_coe_degree_iff (f + g)).mpr hfg,
    (m.withBotDegree_eq_coe_degree_iff f).mpr hf, (m.withBotDegree_eq_coe_degree_iff g).mpr hg]
  first
  | simpa [le_sup_iff] using key
  | simpa [le_sup_iff, toWithBotSyn_apply] using key
  | simp only [toWithBotSyn_apply, WithBot.map_coe, ← WithBot.coe_sup, WithBot.coe_le_coe]
    exact key
