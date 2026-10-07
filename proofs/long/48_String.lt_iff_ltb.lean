/-
Machine-generated proof, verified by Lean.

Theorem:      String.lt_iff_ltb
Source:       Mathlib @ d0a050ad6, Mathlib/Data/String/Basic.lean, line 88
              (added to Mathlib after the model's knowledge cutoff)
Human proof:  32 tactic steps; area: Data
Prover:       Claude (configured model `claude-opus-5-5`), unaided, round 1;
              no Lean access while writing (round 2+ saw Lean's error messages only)
Check:        leanprover/lean4:v4.35.0-rc2, Mathlib's own build options, 0 errors, no `sorry` (1.8 s)

This file shows the statement and the model's proof. It compiles in place: the
model's proof replaces the human proof in the Mathlib file above (see tools/).
-/

theorem lt_iff_ltb {s₁ s₂ : String} :
    s₁ < s₂ ↔ ltb (String.Legacy.iter s₁) (String.Legacy.iter s₂) := by
  have F1 : Legacy.Iterator.hasNext ⟨ofList [], 0⟩ = false := by
    first
    | (simp [Legacy.Iterator.hasNext]; done)
    | (simp [Legacy.Iterator.hasNext, utf8ByteSize_ofList]; done)
    | rfl
    | decide
  have F2 : ∀ (c : Char) (cs : List Char),
      Legacy.Iterator.hasNext ⟨ofList (c :: cs), 0⟩ = true := by
    intro c cs
    have hp : 0 < c.utf8Size := by
      first
      | exact Char.utf8Size_pos c
      | exact Char.utf8Size_pos
      | (unfold Char.utf8Size; split_ifs <;> omega)
    first
    | (simp [Legacy.Iterator.hasNext]; done)
    | (simp [Legacy.Iterator.hasNext]; omega)
    | (simp [Legacy.Iterator.hasNext, Char.utf8Size_pos]; done)
    | (simp [Legacy.Iterator.hasNext, utf8ByteSize_ofList]; omega)
    | (simp [Legacy.Iterator.hasNext, rawEndPos_ofList]; omega)
    | (simp [Legacy.Iterator.hasNext, utf8Len]; omega)
    | (simp [Legacy.Iterator.hasNext, ofList_cons]; omega)
    | exact (Legacy.Iterator.ValidFor.mk (l := []) (r := c :: cs)).hasNext.mpr (List.cons_ne_nil _ _)
  have F3 : ∀ (c : Char) (cs : List Char), Legacy.Iterator.curr ⟨ofList (c :: cs), 0⟩ = c := by
    intro c cs
    first
    | (simp [Legacy.Iterator.curr, Pos.Raw.get, utf8GetAux]; done)
    | exact get_of_valid [] (c :: cs)
    | (simp only [Legacy.Iterator.curr]; exact get_of_valid [] (c :: cs))
    | (simpa [Legacy.Iterator.curr] using get_of_valid [] (c :: cs))
    | (simp [Legacy.Iterator.curr]; done)
    | (simp [Legacy.Iterator.curr, Pos.Raw.get]; done)
    | exact (Legacy.Iterator.ValidFor.mk (l := []) (r := c :: cs)).curr
    | rfl
  have F4 : ∀ (c : Char) (cs : List Char),
      Legacy.Iterator.next ⟨ofList (c :: cs), 0⟩ = ⟨ofList (c :: cs), (0 : Pos.Raw) + c⟩ := by
    intro c cs
    have h := F3 c cs
    first
    | (rw [show Legacy.Iterator.next ⟨ofList (c :: cs), 0⟩ =
          ⟨ofList (c :: cs), (0 : Pos.Raw) + Legacy.Iterator.curr ⟨ofList (c :: cs), 0⟩⟩ from rfl, h];
        done)
    | (simp only [Legacy.Iterator.curr] at h; simp only [Legacy.Iterator.next, Pos.Raw.next, h]; done)
    | (simp only [Legacy.Iterator.curr] at h; simp only [Legacy.Iterator.next, Pos.Raw.next, h]; rfl)
    | (simp only [Legacy.Iterator.curr] at h; simp [Legacy.Iterator.next, Pos.Raw.next, h]; done)
  suffices key : ∀ l₁ l₂ : List Char, l₁ < l₂ ↔ ltb ⟨ofList l₁, 0⟩ ⟨ofList l₂, 0⟩ by
    have := key s₁.toList s₂.toList
    simp only [ofList_toList] at this
    rw [lt_iff_toList_lt]
    first
    | exact this
    | (simpa [Legacy.iter] using this)
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂
    cases l₂ with
    | nil =>
      apply iff_of_false
      · first
        | exact List.not_lt_nil _
        | (simp; done)
        | (intro h; cases h)
      · rw [ltb, F1]
        simp
    | cons c₂ cs₂ =>
      apply iff_of_true
      · first
        | exact List.nil_lt_cons _ _
        | (simp; done)
        | exact List.Lex.nil
      · rw [ltb, F1, F2]
        simp
  | cons c₁ cs₁ ih =>
    intro l₂
    cases l₂ with
    | nil =>
      apply iff_of_false
      · first
        | exact List.not_lt_nil _
        | (simp; done)
        | (intro h; cases h)
      · rw [ltb, F1]
        simp
    | cons c₂ cs₂ =>
      rw [ltb, F2, F2, F3, F3, F4, F4, if_pos rfl, if_pos rfl]
      by_cases h : c₁ = c₂
      · subst h
        rw [if_pos rfl, ltb_cons_addChar, ← ih]
        first
        | (simp; done)
        | exact List.Lex.cons_iff
        | (rw [List.cons_lt_cons_iff]; simp; done)
        | exact ⟨fun hlt => by cases hlt with | cons h' => exact h' | rel h' => exact absurd h' (lt_irrefl _), List.Lex.cons⟩
      · rw [if_neg h]
        first
        | (simp [h]; done)
        | (rw [List.cons_lt_cons_iff]; simp [h]; done)
        | (simp only [decide_eq_true_eq]; exact ⟨fun hlt => by cases hlt <;> simp_all, List.Lex.rel⟩)
