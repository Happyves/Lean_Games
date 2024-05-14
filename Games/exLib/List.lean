/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic
import Mathlib.Data.List.DropRight

def List.minimum! [Preorder α] [@DecidableRel α (· < ·)] (l : List α) (h : l ≠ []) : α :=
  match l with
  | [] => show α from (by contradiction)
  | [x] => x
  | x :: y :: L => let m := (y :: L).minimum! (by exact cons_ne_nil y L)
                   if x < m then x else m

#check List.minimum_of_length_pos -- damit

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


lemma List.rdrop_append.{u} {α : Type u} {l₁ l₂ : List α} (i : ℕ) : List.rdrop (l₁ ++ l₂) (List.length l₂ + i)  = List.rdrop l₁ i:=
  by
  simp_rw [List.rdrop_eq_reverse_drop_reverse, List.reverse_append]
  congr 1
  rw [← List.length_reverse]
  apply List.drop_append




lemma List.filter_eq_if [DecidableEq α] (a b : List α) {P : α → Bool} :
  a.filter P = b → ((∀ x ∈ b, x ∈ a) ∧ (∀ x ∈ a, (x ∈ b ↔ P x))) :=
  -- converse only up to permutation !
  by
  intro c
  constructor
  · intro x xb
    rw [← c] at xb
    exact mem_of_mem_filter xb
  · intro x xa
    constructor
    · intro xb
      rw [← c] at xb
      exact of_mem_filter xb
    · rw [← c]
      exact fun a_1 => mem_filter_of_mem xa a_1


lemma List.cons_head_tail (l : List α) (hl : l ≠ []) : (l.head hl) :: l.tail = l :=
  match l with
  | [] => (by contradiction)
  | x :: l => (by dsimp)


lemma List.cons_eq_singleton_append (l : List α) (x : α) : x :: l = [x] ++ l := by exact rfl


lemma List.exists_min_length_list_of_exists_list {P : List α → Prop} (h : ∃ l : List α, P l) :
  ∃ l : List α, P l ∧ (∀ L : List α, P L → l.length ≤ L.length) :=
  by
  classical
  let S := {n : ℕ | ∃ l : List α, P l ∧ n = l.length}
  have S_ne : S.Nonempty :=
    by
    use (Classical.choose h).length
    dsimp
    use (Classical.choose h)
    constructor
    · exact (Classical.choose_spec h)
    · rfl
  obtain ⟨m,mS,ml⟩ := (@WellFounded.wellFounded_iff_has_min _ Nat.lt).mp (Nat.lt_wfRel.wf) S S_ne
  obtain ⟨l,pl,lm⟩ := mS
  use l
  constructor
  · exact pl
  · intro L pL
    specialize ml L.length (by use L)
    rw [lm] at ml
    rw [← Nat.not_lt]
    apply ml
