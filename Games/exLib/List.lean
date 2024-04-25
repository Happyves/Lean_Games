/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic


def List.minimum! [Preorder α] [@DecidableRel α (· < ·)] (l : List α) (h : l ≠ []) : α :=
  match l with
  | [] => show α from (by contradiction)
  | [x] => x
  | x :: y :: L => let m := (y :: L).minimum! (by exact cons_ne_nil y L)
                   if x < m then x else m


lemma List.ne_empty_iff_exists_mem (L : List α) : L ≠ [] ↔ ∃ a, a ∈ L :=
  by
  constructor
  · intro h
    cases' L with x l
    · contradiction
    · use x
      exact mem_cons_self x l
  · intro ⟨a,adef⟩
    exact ne_nil_of_mem adef


lemma List.filter_eq_iff [DecidableEq α] (a b : List α) {P : α → Bool} :
  a.filter P = b ↔ ((∀ x ∈ b, x ∈ a) ∧ (∀ x ∈ a, (x ∈ b → P x) ∧ (x ∉ b → ¬ P x)) ) :=
  by
  constructor
  · intro c
    constructor
    · intro x xb
      rw [← c] at xb
      exact mem_of_mem_filter xb
    · intro x xa
      constructor
      · intro xb
        rw [← c] at xb
        exact of_mem_filter xb
      · contrapose!
        rw [← c]
        exact fun a_1 => mem_filter_of_mem xa a_1
  · intro ⟨c1,c2⟩
    induction' b with y l ih
    · simp at *
      rw [List.filter_eq_nil]
      simp
      apply c2
    ·
    -- induction' a with x l ih
    -- · rw [List.filter_nil]
    --   cases' b with y b
    --   · rfl
    --   · exfalso
    --     exact (List.not_mem_nil y) (c1 y (by apply List.mem_cons_self))
    -- · rw [List.filter_cons]
    --   split_ifs with q
    --   · specialize c2 x (by apply List.mem_cons_self)
