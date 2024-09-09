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

private lemma scase_cst_cst (sa sb : Fin n → Fin D → Fin n) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∃ x, ∀ (i : Fin n), sb i d = x)
  : sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa ; obtain ⟨ y ,ydef⟩ := qb
  have : x = y := by rw [← xdef ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩, ← ydef ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩] ; nth_rewrite 2 [← Q] ; rw [idef.2.symm ]
  rw [this] at xdef
  rw [xdef, ydef]


private lemma scase_cst_inc (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = i)
  : sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [Q, Function.funext_iff] at idef
    specialize idef d
    convert idef.symm
    -- might of convert ; should be using Fin.fin_one_eq_zero ?
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    by_cases L : x = ⟨0, lt_trans zero_lt_one hn'⟩
    · have oh : sb ⟨1, hn'⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨1, hn'⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨1, hn'⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        rw [qb ⟨1, hn'⟩, xdef j, L, Fin.eq_iff_veq] at jdef
        contradiction
      exact no oh
    · have oh : sb ⟨0, lt_trans zero_lt_one hn'⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨0, lt_trans zero_lt_one hn'⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨0, lt_trans zero_lt_one hn'⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        rw [qb ⟨0, lt_trans zero_lt_one hn'⟩, xdef j] at jdef
        contradiction
      exact no oh


private lemma scase_cst_dec (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [Q, Function.funext_iff] at idef
    specialize idef d
    convert idef.symm
    -- might of convert ; should be using Fin.fin_one_eq_zero ?
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    by_cases L : x = ⟨0, lt_trans zero_lt_one hn'⟩
    · replace idef := idef.2
      rw [Q, Function.funext_iff] at idef
      specialize idef d
      simp_rw [qb ⟨0, lt_trans zero_lt_one hn'⟩, xdef ⟨0, lt_trans zero_lt_one hn'⟩, L, Opp,  Fin.eq_iff_veq, Nat.sub_zero, Nat.sub_eq_zero_iff_le] at idef
      exact (not_le_of_lt hn') idef
    · have oh : sb ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        simp_rw [qb ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩, xdef j, Opp, Nat.sub_self] at jdef
        exfalso
        exact L jdef
      exact no oh


private lemma scase_cst_inc' (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sa i = sb ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = i)
  : sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [Q, Function.funext_iff] at idef
    specialize idef d
    convert idef
    -- might of convert ; should be using Fin.fin_one_eq_zero ?
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    by_cases L : x = ⟨0, lt_trans zero_lt_one hn'⟩
    · have oh : sb ⟨1, hn'⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨1, hn'⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨1, hn'⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        rw [qb ⟨1, hn'⟩, xdef j, L, Fin.eq_iff_veq] at jdef
        contradiction
      exact no oh
    · have oh : sb ⟨0, lt_trans zero_lt_one hn'⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨0, lt_trans zero_lt_one hn'⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨0, lt_trans zero_lt_one hn'⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        rw [qb ⟨0, lt_trans zero_lt_one hn'⟩, xdef j] at jdef
        contradiction
      exact no oh

private lemma scase_inc_dec (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∀ (i : Fin n), sa i d = i) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : sa idx d = sb idx d :=
  by
  rw [Nat.ne_zero_iff_one_le] at hn
  replace idef := idef.2
  rw [Q, Function.funext_iff] at idef
  specialize idef d
  by_cases K : n = 1
  · convert idef.symm
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    specialize qa ⟨0, lt_trans zero_lt_one hn'⟩
    specialize qb ⟨0, lt_trans zero_lt_one hn'⟩
    simp_rw [qa, qb, Opp,  Fin.eq_iff_veq, Nat.sub_zero, Nat.sub_eq_zero_iff_le] at idef
    exact (not_le_of_lt hn') idef


private lemma scase_cst_dec' (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sa i = sb ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [Q, Function.funext_iff] at idef
    specialize idef d
    convert idef
    -- might of convert ; should be using Fin.fin_one_eq_zero ?
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    by_cases L : x = ⟨0, lt_trans zero_lt_one hn'⟩
    · replace idef := idef.2
      rw [Q, Function.funext_iff] at idef
      specialize idef d
      rw [eq_comm] at idef
      simp_rw [qb ⟨0, lt_trans zero_lt_one hn'⟩, xdef ⟨0, lt_trans zero_lt_one hn'⟩, L, Opp,  Fin.eq_iff_veq, Nat.sub_zero, Nat.sub_eq_zero_iff_le] at idef
      exact (not_le_of_lt hn') idef
    · have oh : sb ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        simp_rw [qb ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩, xdef j, Opp, Nat.sub_self] at jdef
        exfalso
        exact L jdef
      exact no oh


private lemma scase_inc_dec' (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sa i = sb ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∀ (i : Fin n), sa i d = i) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : sa idx d = sb idx d :=
  by
  rw [Nat.ne_zero_iff_one_le] at hn
  replace idef := idef.2
  rw [Q, Function.funext_iff] at idef
  specialize idef d
  by_cases K : n = 1
  · convert idef
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    specialize qa ⟨0, lt_trans zero_lt_one hn'⟩
    specialize qb ⟨0, lt_trans zero_lt_one hn'⟩
    rw [eq_comm] at idef
    simp_rw [qa, qb, Opp,  Fin.eq_iff_veq, Nat.sub_zero, Nat.sub_eq_zero_iff_le] at idef
    exact (not_le_of_lt hn') idef



--#exit

lemma seq_rep_line_rel (sa sb : Fin n → (Fin D → Fin n)) (l : Finset (Fin D → Fin n)) (ha : seq_rep_line D n hn sa l) (hb : seq_rep_line D n hn sb l) :
  sa = sb ∨ sa = seq_reverse D n hn sb  :=
  by
  obtain ⟨ ra, radef⟩ := ha
  obtain ⟨ rb, rbdef⟩ := hb
  obtain ⟨ i,idef⟩ :=
    have : sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩  ∈ Finset.image sb .univ :=
      by rw [← rbdef, radef] ; rw [Finset.mem_image] ; use ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
    by rw [Finset.mem_image] at this ; exact this
  by_cases Q : i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩
  · left
    funext idx d
    have qa := ra.idc d
    have qb := rb.idc d
    cases' qa with qa qa qa
    · cases' qb with qb qb qb
      · exact scase_cst_cst D n hn sa sb i idef Q idx d qa qb
      · exact scase_cst_inc D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb
      · exact scase_cst_dec D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb
    · cases' qb with qb qb qb
      · exact (scase_cst_inc' D n hn sb sa l rb rbdef ra radef i idef Q idx d qb qa).symm
      · rw [qa, qb]
      · exact scase_inc_dec D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb
    · cases' qb with qb qb qb
      · exact (scase_cst_dec' D n hn sb sa l rb rbdef ra radef i idef Q idx d qb qa).symm
      · exact (scase_inc_dec' D n hn sb sa l rb rbdef ra radef i idef Q idx d qb qa).symm
      · rw [qa, qb]
  · right
    sorry
    -- jesus fucking christ


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
