/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Pairing
import Mathlib --.Combinatorics.Hall.Basic




variable (D n : ℕ)


lemma Nat.ne_zero_iff_one_le : n ≠ 0 ↔ 1 ≤ n :=
  by rw [Nat.succ_le] ; apply Nat.ne_zero_iff_zero_lt



-- Neg Fin has not enough API ...

variable (hn : n ≠ 0)

def Opp (k : Fin n) : Fin n :=
  ⟨n - 1 - k.val, by rw [Nat.ne_zero_iff_one_le] at hn ; apply Nat.sub_lt_left_of_lt_add ; rw [Nat.le_sub_iff_add_le hn, Nat.succ_le] ; apply k.prop ; apply Nat.sub_lt_left_of_lt_add hn ; rw [← add_assoc] ; apply Nat.lt_add_of_pos_left ; exact Nat.zero_lt_one_add k⟩

lemma Nat.eq_of_sub_self_eq {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) (h : c - a = c - b) : a = b := by
  induction' c with c ih
  · rw [Nat.le_zero] at * ; rw [ha,hb]
  · rw [Nat.le_succ_iff] at *
    cases' ha with ha ha
    · cases' hb with hb hb
      · rw [Nat.succ_sub ha, Nat.succ_sub hb, Nat.succ_inj] at h ; exact ih ha hb h
      · rw [Nat.succ_sub ha, hb, Nat.sub_self] at h ; contradiction
    · cases' hb with hb hb
      · rw [Nat.succ_sub hb, ha, Nat.sub_self] at h ; contradiction
      · rw [ha, hb]

lemma Opp_inj (k q : Fin n) (h : Opp n hn k = Opp n hn q) : k = q := by
  simp_rw [Fin.eq_iff_veq, Opp] at *
  rw [Nat.ne_zero_iff_one_le] at hn
  apply Nat.eq_of_sub_self_eq _ _ h
  · rw [Nat.le_sub_iff_add_le hn, Nat.succ_le]
    exact k.prop
  · rw [Nat.le_sub_iff_add_le hn, Nat.succ_le]
    exact q.prop

lemma Opp_Opp (k : Fin n) : Opp n hn (Opp n hn k) = k := by
  simp_rw [Fin.eq_iff_veq, Opp]
  rw [Nat.sub_sub_self]
  rw [Nat.ne_zero_iff_one_le] at hn
  rw [Nat.le_sub_iff_add_le hn, Nat.succ_le]
  exact k.prop



-- # TTT Setup


inductive in_de_const (s : Fin n → Fin n) : Prop
| cst : (∃ x : Fin n, ∀ i : Fin n, s i = x) → in_de_const s
| inc : (∀ i : Fin n, s i = i) → in_de_const s
| dec : (∀ i : Fin n, s i = Opp n hn i) → in_de_const s


structure seq_is_line (s : Fin n → (Fin D → Fin n)) : Prop where
  idc : ∀ d : Fin D, in_de_const n hn (fun j : Fin n => (s j) d)
  non_pt : ¬ (∀ d : Fin D, (∃ x : Fin n, ∀ j : Fin n, s j d = x))

structure seq_rep_line (s : Fin n → (Fin D → Fin n)) (l : Finset (Fin D → Fin n)) : Prop where
  line : seq_is_line D n hn s
  rep : l = Finset.image s .univ


-- TODO in paper : compare to combi lines of HalesJewett by David Wärn
def is_combi_line (can : Finset (Fin D → Fin n)) : Prop :=
  ∃ s : Fin n → (Fin D → Fin n), seq_rep_line D n hn s can


open Classical

noncomputable
def TTT_win_sets : Finset (Finset (Fin D → Fin n)) := Finset.univ.filter (is_combi_line D n hn)

noncomputable
def TTT := Positional_Game_World (TTT_win_sets D n hn)



-- # Combinatorics of combinatorial lines


lemma incidence_chara (p : Fin D → Fin n) (l : Finset (Fin D → Fin n)) (hl : is_combi_line D n hn l) :
  p ∈ l ↔ (∀ s : Fin n → (Fin D → Fin n), seq_rep_line D n hn s l → ∃ i, s i = p) :=
  by
  constructor
  · intro pl s sdef
    simp_rw [sdef.rep, Finset.mem_image, Finset.mem_univ] at pl
    obtain ⟨i,_,idef⟩ := pl
    exact ⟨i,idef⟩
  · intro A
    obtain ⟨r, rdef⟩ := hl
    specialize A r rdef
    simp_rw [rdef.rep, Finset.mem_image, Finset.mem_univ]
    obtain ⟨i,idef⟩ := A
    exact ⟨i, True.intro, idef⟩


def seq_reverse (s : Fin n → (Fin D → Fin n)) : Fin n → (Fin D → Fin n) :=
  fun i d => (s (Opp n hn i) d)

lemma seq_reverse_of_line_is_line (s : Fin n → (Fin D → Fin n)) (h : seq_is_line D n hn s) :
  seq_is_line D n hn (seq_reverse D n hn s) :=
  by
  constructor
  · intro d
    replace h := h.idc d
    cases' h with cst inc dec
    · apply in_de_const.cst
      obtain ⟨x,cst⟩ := cst
      use x
      intro i
      dsimp [seq_reverse]
      apply cst
    · apply in_de_const.dec
      intro i
      dsimp [seq_reverse]
      rw [inc]
    · apply in_de_const.inc
      intro i
      dsimp [seq_reverse]
      rw [dec]
      rw [Opp_Opp]
  · replace h := h.non_pt
    contrapose! h
    intro d
    obtain ⟨x,xdef⟩ := h d
    use x
    intro j
    dsimp [seq_reverse] at xdef
    specialize xdef (Opp n hn j)
    convert xdef
    rw [Opp_Opp]





lemma seq_rep_line_rel (sa sb : Fin n → (Fin D → Fin n)) (l : Finset (Fin D → Fin n)) (ha : seq_rep_line D n hn sa l) (hb : seq_rep_line D n hn sb l) :
  sa = sb ∨ sa = seq_reverse D n hn sb  :=
  by
  sorry

#exit

lemma combi_line_repr_card (l : Finset (Fin D → Fin n)) (hl : is_combi_line D n l) :
  (Finset.univ.filter (fun c : Fin n → (Fin D → Fin n) => seq_rep_line D n s l)).card = 2 :=
  by
  -- get the first line by unfolding hl, then the second by considering its negative, and use thm to show that those are all,
  -- aka show Finset.univ.filter (fun c : Fin n → (Fin D → Fin n) => seq_rep_line D n s l) = the set of these two lines






#exit
lemma incidence_ub (p : Fin D → Fin n) :
  (Finset.univ.filter (fun c : Finset (Fin D → Fin n) => is_combi_line D n c ∧ p ∈ c)).card ≤ (3^D - 1)/2 :=
  by sorry





#exit

-- Both depend on classical choice, so making a constructive pairing strat would be mildly pointless for this project
#print axioms Finset.all_card_le_biUnion_card_iff_existsInjective'
#print axioms Fintype.all_card_le_rel_image_card_iff_exists_injective
