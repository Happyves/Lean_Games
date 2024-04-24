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
