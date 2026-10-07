/-
Machine-generated proof, verified by Lean.

Theorem:      intermediate_value_Ioi
Source:       Mathlib @ d0a050ad6, Mathlib/Topology/Order/IntermediateValue.lean, line 708
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  3 tactic steps; area: Topology
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (2.7 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem intermediate_value_Ioi {a : α} {f : α → δ} (hf : ContinuousOn f (Ici a))
    (htop : Tendsto f atTop atTop) : Ioi (f a) ⊆ f '' Ioi a := by
  intro y hy
  have : Nonempty α := ⟨a⟩
  have hev : ∀ᶠ x in atTop, y ≤ f x ∧ a ≤ x := by
    first
    | exact (htop.eventually_ge_atTop y).and (eventually_ge_atTop a)
    | exact (htop.eventually (eventually_ge_atTop y)).and (eventually_ge_atTop a)
  obtain ⟨b, hb, hab⟩ := hev.exists
  have hy' : y ∈ Ioc (f a) (f b) := ⟨hy, hb⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioc hab (hf.mono Icc_subset_Ici_self) hy'
  exact ⟨c, hc.1, hfc⟩
