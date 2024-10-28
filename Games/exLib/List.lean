/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Data.List.DropRight
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

-- # To Mathlib

lemma List.length_rtake {l : List α} {t : Nat} (ht : t ≤ l.length) : (l.rtake t).length = t := by
  unfold List.rtake ; rw [List.length_drop] ; apply Nat.sub_sub_self ht


def List.rget (l : List α) (t : Fin l.length) := l.get ⟨l.length - 1 - t, (by rw [Nat.sub_sub] ; apply Nat.sub_lt_self (by apply Nat.add_pos_left ; exact zero_lt_one) (by rw [add_comm, Nat.succ_le] ; apply t.prop) )⟩

lemma List.rget_cons_rtake {l : List α} {t : Fin l.length} : l.rtake (t+1) = (l.rget t) :: (l.rtake t) := by
  unfold List.rtake List.rget
  rw [Nat.sub_succ', tsub_right_comm]
  cases' l with x l
  · have no := t.prop
    contradiction
  · simp_rw [List.length_cons, Nat.succ_sub_one]
    rw [show Nat.succ (length l) - ↑t = Nat.succ (length l - ↑t) from (by apply Nat.succ_sub ; have := t.prop ; simp_rw [List.length_cons] at this ; rw [Nat.lt_succ] at this ; exact this)]
    apply List.drop_eq_getElem_cons

lemma List.rtake_cons_eq_self {l : List α} {x : α} {t : Nat} (ht : t ≤ l.length) : ((x :: l).rtake t) = (l.rtake t) := by
  unfold List.rtake
  rw [List.length_cons, Nat.succ_sub ht]
  rfl


lemma List.rget_cons_eq_self {l : List α} {x : α} {t : Fin l.length} : (x :: l).rget ⟨t.val, (by rw [List.length_cons] ; apply lt_trans t.prop ; apply Nat.lt_succ_self) ⟩ = l.rget t := by
  unfold List.rget
  simp_rw [List.length_cons]
  simp_rw [Nat.succ_sub (show 1 ≤ l.length by by_contra! con ; rw [Nat.lt_one_iff] at con ; have := t.prop ; simp_rw [con] at this ; contradiction)]
  simp_rw [Nat.succ_sub (show t ≤ l.length - 1 by apply Nat.le_sub_one_of_lt ; exact t.prop)]
  rfl


lemma List.rget_cons_length {l : List α} {x : α} : (x :: l).rget ⟨l.length, (by rw [List.length_cons] ; exact Nat.le.refl)⟩ = x := by
  unfold List.rget
  dsimp
  simp_rw [Nat.sub_self]
  apply List.get_cons_zero

lemma List.rtake_length {l : List α}  : l.rtake l.length = l := by
  unfold List.rtake ; rw [Nat.sub_self] ; apply List.drop_zero




lemma List.rtake_all_of_le {α : Type _} {n : ℕ} {l : List α} (h : List.length l ≤ n) : l.rtake n  = l := by
  unfold List.rtake ; rw [Nat.sub_eq_zero_of_le h]  ; apply List.drop_zero

lemma List.length_le_of_suffix (m : l <:+ L) : l.length ≤ L.length := by
  rw [List.suffix_iff_eq_append] at m
  rw [← m, List.length_append]
  exact Nat.le_add_left (length l) (length (take (length L - length l) L))




lemma List.rget_suffix {α : Type _} {l L : List α} (m : l <:+ L) (n : Fin l.length) : L.rget ⟨n.val, by apply lt_of_lt_of_le n.prop (List.length_le_of_suffix m)⟩ = l.rget n := by
  rw [List.suffix_iff_eq_append] at m
  have : (take (length L - length l) L ++ l).rget { val := ↑n, isLt := by rw [m] ; rw [← List.suffix_iff_eq_append] at m ; apply lt_of_lt_of_le n.prop (List.length_le_of_suffix m) } = rget l n := by
    unfold List.rget
    rw [List.get_append_right]
    · dsimp
      congr 2
      simp_rw [List.length_append]
      cases' l with x l
      · have := n.prop
        contradiction
      · rw [Nat.add_sub_assoc (by rw [List.length_cons] ; linarith)]
        rw [Nat.add_sub_assoc (by rw [← Nat.pred_eq_sub_one] ; apply Nat.le_pred_of_lt ; exact n.prop )]
        rw [Nat.add_sub_cancel_left]
    · dsimp
      simp_rw [List.length_append, not_lt]
      cases' l with x l
      · have := n.prop
        contradiction
      · rw [Nat.add_sub_assoc (by rw [List.length_cons] ; linarith)]
        rw [Nat.add_sub_assoc (by rw [← Nat.pred_eq_sub_one] ; apply Nat.le_pred_of_lt ; exact n.prop )]
        exact Nat.le_add_right (length (take (length L - length (x :: l)) L)) (length (x :: l) - 1 - ↑n)
    · dsimp
      simp_rw [List.length_append]
      cases' l with x l
      · have := n.prop
        contradiction
      · rw [Nat.add_sub_assoc (by rw [List.length_cons] ; linarith)]
        rw [Nat.add_sub_assoc (by rw [← Nat.pred_eq_sub_one] ; apply Nat.le_pred_of_lt ; exact n.prop )]
        rw [Nat.add_sub_cancel_left]
        rw [Nat.sub_sub]
        apply Nat.sub_lt
        · rw [List.length_cons] ; linarith
        · rw [add_comm]
          apply Nat.zero_lt_succ
  convert this
  rw [m]

#check List.getElem_append_right

lemma List.rtake_suffix_comm (M : List.rtake hist (List.length h) <:+ h) (L : List.length hist ≤ List.length h) : hist = List.rtake h (List.length hist) := by
  rw [List.rtake_all_of_le L] at M
  induction' hist with x l ih
  · dsimp ; rw [List.rtake_zero]
  · rw [List.length_cons]
    have : length l < length h := by apply lt_of_lt_of_le _ L ; rw [List.length_cons] ; apply Nat.lt_succ_self
    rw [@List.rget_cons_rtake _ _ ⟨l.length, this ⟩]
    congr
    · rw [eq_comm]
      rw [List.rget_suffix M ⟨l.length, by rw [List.length_cons] ; linarith⟩ ]
      apply List.rget_cons_length
    · apply ih _ (le_of_lt this)
      apply IsSuffix.trans _ M
      exact suffix_cons x l

lemma List.rget_singleton {x : α} {n : Fin 1} : [x].rget n = x := by
  unfold List.rget ; apply List.getElem_singleton


theorem List.rdrop_append_rtake : ∀ (n : Nat) (l : List α), List.rdrop l n ++ List.rtake l n = l :=
  by
  unfold List.rdrop List.rtake
  intro n l
  apply List.take_append_drop



lemma List.cons_eq_singleton_append (l : List α) (x : α) : x :: l = [x] ++ l := by exact rfl


#exit


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
