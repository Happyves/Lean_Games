/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib


variable (D n : ℕ)


lemma Nat.ne_zero_iff_one_le : n ≠ 0 ↔ 1 ≤ n :=
  by rw [Nat.succ_le] ; apply Nat.ne_zero_iff_zero_lt


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

lemma seq_reverse_of_line_rep_line (l : Finset (Fin D → Fin n)) (s : Fin n → (Fin D → Fin n)) (h : seq_rep_line D n hn s l) :
  seq_rep_line D n hn (seq_reverse D n hn s) l :=
  by
  constructor
  · apply seq_reverse_of_line_is_line
    exact h.line
  · replace h := h.rep
    rw [h]
    ext x
    simp_rw [Finset.mem_image]
    constructor
    · rintro ⟨i,idef⟩
      use Opp n hn i
      constructor
      · apply Finset.mem_univ
      · unfold seq_reverse
        simp_rw [Opp_Opp, idef.2]
    · rintro ⟨i,idef⟩
      use Opp n hn i
      constructor
      · apply Finset.mem_univ
      · unfold seq_reverse at idef
        apply idef.2




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


private lemma ocase_cst_cst (sa sb : Fin n → Fin D → Fin n) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∃ x, ∀ (i : Fin n), sb i d = x)
  : sa idx d = (seq_reverse D n hn sb) idx d :=
  by
  obtain ⟨x,xdef⟩ := qa ; obtain ⟨ y ,ydef⟩ := qb
  have : x = y := by
    specialize xdef ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩
    specialize ydef i
    rw [idef.2] at ydef
    rw [← xdef, ← ydef]
  rw [this] at xdef
  dsimp [seq_reverse]
  rw [xdef, ydef]


private lemma ocase_cst_inc (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : ¬ i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = i)
  : sa idx d = seq_reverse D n hn sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [ Function.funext_iff] at idef
    specialize idef d
    dsimp [seq_reverse]
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


lemma Nat.sub_eq_self {n m : Nat} (hn : n ≠ 0) : n - m = n ↔ m = 0 := by
  constructor
  · intro h
    induction' n with n ih
    · contradiction
    · have : m ≤ n := by
        by_contra! con
        rw [← Nat.succ_le, ← Nat.sub_eq_zero_iff_le] at con
        rw [con] at h
        exact hn h.symm
      rw [Nat.succ_sub this, Nat.succ_inj] at h
      by_cases q : n = 0
      · rwa [q, Nat.le_zero] at this
      · exact ih q h
  · intro h ; rw [h, Nat.sub_zero]

private lemma ocase_cst_dec (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : ¬ i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : sa idx d = seq_reverse D n hn sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [Function.funext_iff] at idef
    specialize idef d
    dsimp [seq_reverse]
    convert idef.symm
    -- might of convert ; should be using Fin.fin_one_eq_zero ?
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    by_cases L : x = ⟨n-1, Nat.sub_lt_self zero_lt_one hn ⟩
    · replace idef := idef.2
      rw [Function.funext_iff] at idef
      specialize idef d
      simp_rw [qb i, xdef ⟨0, lt_trans zero_lt_one hn'⟩, L, Opp,  Fin.eq_iff_veq] at idef
      rw [@Nat.sub_eq_self  (n-1) _ (by rw [Nat.sub_ne_zero_iff_lt] ; exact hn')] at idef
      simp_rw [Fin.eq_iff_veq] at Q
      exact Q idef
    · have oh : sb ⟨0, lt_trans zero_lt_one hn'⟩ ∈ l := by
        rw [rbdef] ; rw [Finset.mem_image] ; use ⟨0, lt_trans zero_lt_one hn'⟩ ; exact ⟨ Finset.mem_univ _ , rfl⟩
      have no : sb ⟨0, lt_trans zero_lt_one hn'⟩ ∉ l := by
        rw [radef, Finset.mem_image] at oh
        obtain ⟨j,jdef⟩ := oh
        replace jdef := jdef.2
        rw [Function.funext_iff] at jdef
        specialize jdef d
        simp_rw [qb ⟨0, lt_trans zero_lt_one hn'⟩, xdef j, Opp] at jdef
        exfalso
        exact L jdef
      exact no oh


private lemma ocase_cst_inc' (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sa i = sb ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : ¬ i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = i)
  : seq_reverse D n hn sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [ Function.funext_iff] at idef
    specialize idef d
    dsimp [seq_reverse]
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


private lemma ocase_inc_inc (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : ¬ i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∀ (i : Fin n), sa i d = i) (qb : ∀ (i : Fin n), sb i d = i)
  : sa idx d = seq_reverse D n hn sb idx d :=
  by
  rw [Nat.ne_zero_iff_one_le] at hn
  replace idef := idef.2
  rw [Function.funext_iff] at idef
  specialize idef d
  by_cases K : n = 1
  · dsimp [seq_reverse]
    convert idef.symm
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    specialize qa ⟨0, lt_trans zero_lt_one hn'⟩
    specialize qb i
    simp_rw [qa, qb] at idef
    exact Q idef


private lemma ocase_cst_dec' (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sa i = sb ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : ¬ i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∃ x, ∀ (i : Fin n), sa i d = x) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : seq_reverse D n hn sa idx d = sb idx d :=
  by
  obtain ⟨x,xdef⟩ := qa
  rw [Nat.ne_zero_iff_one_le] at hn
  by_cases K : n = 1
  · replace idef := idef.2
    rw [Function.funext_iff] at idef
    specialize idef d
    dsimp [seq_reverse]
    convert idef
    -- might of convert ; should be using Fin.fin_one_eq_zero ?
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    by_cases L : x = ⟨0, lt_trans zero_lt_one hn'⟩
    · replace idef := idef.2
      rw [Function.funext_iff] at idef
      specialize idef d
      rw [eq_comm] at idef
      simp_rw [qb ⟨0, lt_trans zero_lt_one hn'⟩, xdef i, L, Opp,  Fin.eq_iff_veq, Nat.sub_zero, Nat.sub_eq_zero_iff_le] at idef
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

private lemma ocase_dec_dec (sa sb : Fin n → Fin D → Fin n) (l : Finset (Fin D → Fin n)) (ra : seq_is_line D n hn sa) (radef : l = Finset.image sa Finset.univ)
  (rb : seq_is_line D n hn sb) (rbdef : l = Finset.image sb Finset.univ) (i : Fin n) (idef : i ∈ Finset.univ ∧ sb i = sa ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩)
  (Q : ¬ i = ⟨0, Nat.pos_iff_ne_zero.mpr hn⟩) (idx : Fin n) (d : Fin D) (qa : ∀ (i : Fin n), sa i d = Opp n hn i) (qb : ∀ (i : Fin n), sb i d = Opp n hn i)
  : sa idx d = seq_reverse D n hn sb idx d :=
  by
  rw [Nat.ne_zero_iff_one_le] at hn
  replace idef := idef.2
  rw [Function.funext_iff] at idef
  specialize idef d
  by_cases K : n = 1
  · dsimp [seq_reverse]
    convert idef.symm
  · exfalso
    have hn' : 1 < n := by apply lt_of_le_of_ne hn (by rw [ne_comm] ; apply K)
    specialize qa ⟨0, lt_trans zero_lt_one hn'⟩
    specialize qb i
    simp_rw [qa, qb] at idef
    exact Q (Opp_inj _ _ _ _ idef)



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
    funext idx d
    have qa := ra.idc d
    have qb := rb.idc d
    cases' qa with qa qa qa
    · cases' qb with qb qb qb
      · exact ocase_cst_cst D n hn sa sb i idef idx d qa qb
      · exact ocase_cst_inc D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb
      · exact ocase_cst_dec D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb
    · cases' qb with qb qb qb
      · exact (ocase_cst_inc' D n hn sb sa l rb rbdef ra radef i idef Q idx d qb qa).symm
      · exact ocase_inc_inc D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb
      · dsimp [seq_reverse]
        replace qb := fun i => qb (Opp n hn i)
        simp_rw [Opp_Opp] at qb
        rw [qa,qb]
    · cases' qb with qb qb qb
      · exact (ocase_cst_dec' D n hn sb sa l rb rbdef ra radef i idef Q idx d qb qa).symm
      · dsimp [seq_reverse]
        replace qb := fun i => qb (Opp n hn i)
        rw [qa,qb]
      · exact ocase_dec_dec D n hn sa sb l ra radef rb rbdef i idef Q idx d qa qb


variable (Hn : 1 < n)

lemma strengthen : n ≠ 0 :=
  by
  intro con
  rw [con, ← not_le] at Hn
  apply Hn zero_le_one

lemma seq_ne_seq_reverse (s : Fin n → (Fin D → Fin n)) (l : Finset (Fin D → Fin n))  (h : seq_rep_line D n (strengthen n Hn) s l) :
  s ≠ (seq_reverse D n (strengthen n Hn) s) :=
  by
  intro con
  have remind := h.line.non_pt
  rw [not_forall] at remind
  obtain ⟨d, dp⟩ := remind
  have remind := h.line.idc d
  cases' remind with cst inc dec
  · exact dp cst
  · have := inc ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
    rw [con] at this
    simp_rw [seq_reverse] at this
    specialize inc (Opp n (strengthen n Hn) ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩)
    simp_rw [this, Opp, Fin.eq_iff_veq, Nat.sub_zero] at inc
    exact (Nat.sub_ne_zero_of_lt Hn) inc.symm
  · have := dec ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
    rw [con] at this
    simp_rw [seq_reverse] at this
    specialize dec (Opp n (strengthen n Hn) ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩)
    simp_rw [this, Opp, Fin.eq_iff_veq, Nat.sub_zero, Nat.sub_self] at dec
    exact (Nat.sub_ne_zero_of_lt Hn) dec


open Classical


-- unused
lemma combi_line_repr_card (l : Finset (Fin D → Fin n)) (hl : is_combi_line D n (strengthen n Hn) l) :
  (Finset.univ.filter (fun c : Fin n → (Fin D → Fin n) => seq_rep_line D n (strengthen n Hn) c l)).card = 2 :=
  by
  obtain ⟨fst, fst_p⟩ := hl
  let snd := seq_reverse D n (strengthen n Hn) fst
  have snd_p := seq_reverse_of_line_rep_line D n (strengthen n Hn) l fst fst_p
  have : (Finset.univ.filter (fun c : Fin n → (Fin D → Fin n) => seq_rep_line D n (strengthen n Hn) c l)) = {fst,snd} :=
    by
    ext x
    rw [Finset.mem_filter]
    constructor
    · intro H
      replace H := seq_rep_line_rel D n (strengthen n Hn) x fst l H.2 fst_p
      rw [Finset.mem_insert]
      cases' H with H H
      · left ; exact H
      · right
        rw [Finset.mem_singleton]
        exact H
    · intro H
      rw [Finset.mem_insert, Finset.mem_singleton] at H
      constructor
      · apply Finset.mem_univ
      · cases' H with H H
        · rw [H] ; exact fst_p
        · rw [H] ; exact snd_p
  rw [this]
  simp_rw [Finset.card_insert_eq_ite, Finset.mem_singleton, Finset.card_singleton]
  rw [if_neg]
  apply seq_ne_seq_reverse D n Hn fst l fst_p



private lemma count_below (p : Fin D → Fin n) (b : Finset (Fin D → Fin n)) (bp : is_combi_line D n (strengthen n Hn) b ∧ p ∈ b) :
  (Finset.bipartiteBelow (seq_rep_line D n (strengthen n Hn)) (Finset.filter (fun c => seq_is_line D n (strengthen n Hn) c ∧ p ∈ Finset.image c Finset.univ) Finset.univ) b).card = 2 :=
  by
  rw [Finset.bipartiteBelow, Finset.filter_filter]
  have simpli : ∀ a : Fin n → Fin D → Fin n, ((seq_is_line D n (strengthen n Hn) a ∧ p ∈ Finset.image a Finset.univ) ∧ seq_rep_line D n (strengthen n Hn) a b) ↔ p ∈ Finset.image a Finset.univ ∧ seq_rep_line D n (strengthen n Hn) a b :=
    by
    intro a
    constructor
    · intro h
      exact ⟨h.1.2, h.2⟩
    · intro h
      exact ⟨⟨h.2.line,h.1⟩, h.2⟩
  simp_rw [simpli]
  clear simpli
  obtain ⟨fst, fst_p⟩ := bp.1
  let snd := seq_reverse D n (strengthen n Hn) fst
  have snd_p := seq_reverse_of_line_rep_line D n (strengthen n Hn) b fst fst_p
  have : (Finset.univ.filter (fun c : Fin n → (Fin D → Fin n) => (p ∈ Finset.image c Finset.univ) ∧ seq_rep_line D n (strengthen n Hn) c b)) = {fst,snd} :=
    by
    ext x
    rw [Finset.mem_filter]
    constructor
    · intro H
      replace H := seq_rep_line_rel D n (strengthen n Hn) x fst b H.2.2 fst_p
      rw [Finset.mem_insert]
      cases' H with H H
      · left ; exact H
      · right
        rw [Finset.mem_singleton]
        exact H
    · intro H
      rw [Finset.mem_insert, Finset.mem_singleton] at H
      constructor
      · apply Finset.mem_univ
      · cases' H with H H
        · rw [H, ← fst_p.rep] ; exact ⟨bp.2,fst_p⟩
        · rw [H, ← snd_p.rep] ; exact ⟨bp.2,snd_p⟩
  rw [this]
  simp_rw [Finset.card_insert_eq_ite, Finset.mem_singleton, Finset.card_singleton]
  rw [if_neg]
  apply seq_ne_seq_reverse D n Hn fst b fst_p


#check Finset.filter_filter


private lemma count_above (p : Fin D → Fin n) (a : Fin n → (Fin D → Fin n)) (ha : seq_is_line D n (strengthen n Hn) a ∧ p ∈ Finset.image a Finset.univ):
  (Finset.bipartiteAbove (seq_rep_line D n (strengthen n Hn)) (Finset.filter (fun c => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c) Finset.univ) a).card = 1 :=
  by
  let l := Finset.image a Finset.univ
  have : (Finset.bipartiteAbove (seq_rep_line D n (strengthen n Hn)) (Finset.filter (fun c => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c) Finset.univ) a) = {l} :=
    by
    rw [Finset.bipartiteAbove, Finset.filter_filter]
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro H
      rw [H.2.2.rep]
    · intro H
      constructor
      · apply Finset.mem_univ
      · rw [H]
        exact ⟨⟨⟨a,⟨ha.1, rfl⟩⟩ ,ha.2⟩,⟨ha.1, rfl⟩⟩
  rw [this, Finset.card_singleton]





--#exit

private lemma double_count_lines_seq_main (p : Fin D → Fin n) :
  let t := (Finset.univ.filter (fun c : Finset (Fin D → Fin n) => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c))
  let s := (Finset.univ.filter (fun c : (Fin n → Fin D → Fin n) => seq_is_line D n (strengthen n Hn) c ∧ p ∈ (Finset.univ.image c)))
  let r := seq_rep_line D n (strengthen n Hn)
  (Finset.sum s fun a => (Finset.bipartiteAbove r t a).card) = Finset.sum t fun b => (Finset.bipartiteBelow r s b).card :=
  by apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow


private lemma double_count_lines_seq (p : Fin D → Fin n) :
  (Finset.filter (fun c => seq_is_line D n (strengthen n Hn) c ∧ p ∈ Finset.image c Finset.univ) Finset.univ).card = Finset.sum (Finset.filter (fun c => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c) Finset.univ) (fun _ => 2) :=
  by
  have := double_count_lines_seq_main D n Hn p
  dsimp at this
  have surgery_1 :
    (Finset.sum (Finset.filter (fun c => seq_is_line D n (strengthen n Hn) c ∧ p ∈ Finset.image c Finset.univ) Finset.univ) (fun a => (Finset.bipartiteAbove (seq_rep_line D n (strengthen n Hn)) (Finset.filter (fun c => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c) Finset.univ) a).card)) =
    (Finset.sum (Finset.filter (fun c => seq_is_line D n (strengthen n Hn) c ∧ p ∈ Finset.image c Finset.univ) Finset.univ) (fun _ => 1)) :=
    by apply Finset.sum_congr ; rfl ; intro a ha ; rw [Finset.mem_filter] at ha ; exact count_above D n Hn p a ha.2
  have surgery_2 :
    Finset.sum (Finset.filter (fun c => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c) Finset.univ) (fun b => (Finset.bipartiteBelow (seq_rep_line D n (strengthen n Hn)) (Finset.filter (fun c => seq_is_line D n (strengthen n Hn) c ∧ p ∈ Finset.image c Finset.univ) Finset.univ) b).card) =
    Finset.sum (Finset.filter (fun c => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c) Finset.univ) (fun _ => 2) :=
    by apply Finset.sum_congr ; rfl ; intro b hb ; rw [Finset.mem_filter] at hb ; exact count_below D n Hn p b hb.2
  rw [surgery_1, surgery_2] at this
  rw [Finset.card_eq_sum_ones]
  exact this



-- Goal is to bring set in injection with
#check (.univ : Finset (Fin D → Fin 3)) \ {fun _ => 0}
-- Who's cardinal can be computed with
#check Fintype.card_fin
#check Fintype.card_fun
#check Finset.card_univ
#check Finset.card_sdiff

-- fun _ => 0 represents constant coord sequenc
-- in the injection, the reverse map will send 0 to the corresponding dimension of p
#check Finset.card_congr
#check Finset.card_le_card_of_inj_on


#check Finset.card_attach

private def the_inj (c : (Fin n → Fin D → Fin n)) : Fin D → Fin 3 :=
  fun d =>
    if (∃ x : Fin n, ∀ i : Fin n, c i d = x)
    then
      0
    else
      if (∀ i : Fin n, c i d = i)
      then
        1
      else
        2

-- ↑ is decidable due to nice API
--#print axioms the_inj

private lemma the_inj_zero_iff (c : (Fin n → Fin D → Fin n)) (d : Fin D) : (the_inj D n c) d = 0 ↔ ∃ x : Fin n, ∀ i : Fin n, c i d = x :=
  by
  constructor
  · intro h
    contrapose h
    unfold the_inj
    rw [if_neg h]
    split_ifs
    · decide
    · decide
  · intro h
    unfold the_inj
    rw [if_pos h]

private lemma inc_not_const (c : (Fin n → Fin D → Fin n)) (d : Fin D) (h : ∀ (i : Fin n), c i d = i) : ¬ ∃ x, ∀ (i : Fin n), c i d = x :=
  by
  contrapose! h
  obtain ⟨x, xdef⟩ := h
  by_cases K : x = ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
  · use ⟨1,Hn⟩
    rw [xdef, K]
    intro con
    simp_rw [Fin.eq_iff_veq] at con
  · use ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
    rw [xdef]
    exact K


private lemma the_inj_one_iff (c : (Fin n → Fin D → Fin n)) (d : Fin D) : (the_inj D n c) d = 1 ↔ (∀ i : Fin n, c i d = i) :=
  by
  constructor
  · intro h
    contrapose h
    unfold the_inj
    rw [if_neg h]
    split_ifs
    · decide
    · decide
  · intro h
    unfold the_inj
    rw [if_neg (inc_not_const D n Hn c d h) ,if_pos h]

private lemma dec_not_const (c : (Fin n → Fin D → Fin n)) (d : Fin D) (h : ∀ i : Fin n, c i d = Opp n (strengthen n Hn) i) : ¬ ∃ x, ∀ (i : Fin n), c i d = x :=
  by
  contrapose! h
  obtain ⟨x, xdef⟩ := h
  by_cases K : x = ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
  · use ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
    rw [xdef, K, Opp]
    intro con
    simp_rw [Fin.eq_iff_veq,Nat.sub_zero] at con
    exact (Nat.sub_ne_zero_of_lt Hn) con.symm
  · use ⟨n-1, Nat.sub_lt_self zero_lt_one (le_of_lt Hn) ⟩
    rw [xdef,Opp]
    intro con
    simp_rw [Fin.eq_iff_veq, Nat.sub_self] at con
    apply K
    rw [Fin.eq_iff_veq]
    apply con



private lemma dec_not_inc (c : (Fin n → Fin D → Fin n)) (d : Fin D) (h : ∀ i : Fin n, c i d = Opp n (strengthen n Hn) i) : ¬ ∀ (i : Fin n), c i d = i :=
  by
  push_neg
  use ⟨0,by rw [Nat.pos_iff_ne_zero] ; exact (strengthen n Hn) ⟩
  rw [h, Opp]
  intro con
  simp_rw [Fin.eq_iff_veq,Nat.sub_zero] at con
  exact (Nat.sub_ne_zero_of_lt Hn) con

--#exit

private lemma the_inj_else_iff (c : (Fin n → Fin D → Fin n)) (hc : seq_is_line D n (strengthen n Hn) c) (d : Fin D) : ((the_inj D n c) d ≠ 0 ∧ (the_inj D n c) d ≠ 1) ↔ (∀ i : Fin n, c i d = Opp n (strengthen n Hn) i) :=
  by
  constructor
  · intro h
    contrapose h
    unfold the_inj
    replace hc := hc.idc d
    cases' hc with cst inc dec
    · simp_rw [if_pos cst]
      rw [not_and_or,not_not]
      left
      rfl
    · simp_rw [if_neg (inc_not_const D n Hn c d inc),if_pos inc]
      simp_rw [not_and_or,not_not]
      right
      exact True.intro
    · exfalso
      exact h dec
  · intro h
    unfold the_inj
    rw [if_neg (dec_not_const D n Hn c d h), if_neg (dec_not_inc D n Hn c d h)]
    decide



private lemma the_inj_map (p : Fin D → Fin n) (c : Fin n → Fin D → Fin n) (hc : c ∈ (Finset.univ.filter (fun c : (Fin n → Fin D → Fin n) => seq_is_line D n (strengthen n Hn) c ∧ p ∈ (Finset.univ.image c)))) :
  the_inj D n c ∈ (Finset.univ) \ {fun _ => 0} :=
  by
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  refine' ⟨Finset.mem_univ _ , _ ⟩
  intro con
  simp_rw [Function.funext_iff, the_inj_zero_iff] at con
  rw [Finset.mem_filter] at hc
  exact hc.2.1.non_pt con

private lemma the_inj_inj (p : Fin D → Fin n)
  (a : Fin n → Fin D → Fin n) (ha : a ∈ (Finset.univ.filter (fun c : (Fin n → Fin D → Fin n) => seq_is_line D n (strengthen n Hn) c ∧ p ∈ (Finset.univ.image c))))
  (b : Fin n → Fin D → Fin n) (hb : b ∈ (Finset.univ.filter (fun c : (Fin n → Fin D → Fin n) => seq_is_line D n (strengthen n Hn) c ∧ p ∈ (Finset.univ.image c))))
  (main : the_inj D n a = the_inj D n b) :
  a = b :=
  by
  rw [Finset.mem_filter, Finset.mem_image] at ha hb
  ext i d
  rw [Function.funext_iff] at main
  specialize main d
  unfold the_inj at main
  by_cases Q : (∃ x : Fin n, ∀ i : Fin n, b i d = x)
  · rw [if_pos Q] at main
    have := (the_inj_zero_iff D n a d).mp main
    obtain ⟨y,ydef⟩ := Q
    obtain ⟨x,xdef⟩ := this
    rw [xdef,ydef]
    obtain ⟨ia,iadef⟩ := ha.2.2
    obtain ⟨ib,ibdef⟩ := hb.2.2
    specialize xdef ia
    specialize ydef ib
    rw [iadef.2] at xdef
    rw [ibdef.2] at ydef
    rw [← xdef, ← ydef]
  · by_cases K : (∀ i : Fin n, b i d = i)
    · rw [if_neg Q, if_pos K] at main
      have := (the_inj_one_iff D n Hn a d).mp main
      rw [K, this]
    · rw [if_neg Q, if_neg K] at main
      have := (the_inj_else_iff D n Hn a ha.2.1 d).mp (by unfold the_inj ; rw [main] ; decide)
      cases' hb.2.1.idc d with cst inc dec
      · exfalso ; exact Q cst
      · exfalso ; exact K inc
      · rw [this, dec]

private lemma inj_bd (p : Fin D → Fin n) : (Finset.univ.filter (fun c : (Fin n → Fin D → Fin n) => seq_is_line D n (strengthen n Hn) c ∧ p ∈ (Finset.univ.image c))).card ≤ ((Finset.univ : Finset (Fin D → Fin 3)) \ {fun _ => 0}).card :=
  Finset.card_le_card_of_inj_on (the_inj D n) (fun c hc => the_inj_map D n Hn p c hc) (fun a ha b hb => the_inj_inj D n Hn p a ha b hb)



lemma seq_ub (p : Fin D → Fin n) :
  (Finset.univ.filter (fun c : (Fin n → Fin D → Fin n) => seq_is_line D n (strengthen n Hn) c ∧ p ∈ (Finset.univ.image c))).card ≤ (3^D - 1) :=
  by
  have := (inj_bd D n Hn p)
  rw [Finset.card_sdiff (by exact Finset.subset_univ {fun _ => 0}), Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Finset.card_singleton] at this
  exact this


lemma incidence_ub (p : Fin D → Fin n) :
  (Finset.univ.filter (fun c : Finset (Fin D → Fin n) => is_combi_line D n (strengthen n Hn) c ∧ p ∈ c)).card ≤ (3^D - 1)/2 :=
  by
  rw [Nat.le_div_iff_mul_le (by decide), Finset.card_eq_sum_ones, Finset.sum_mul]
  simp_rw [one_mul]
  rw [← double_count_lines_seq D n Hn]
  apply seq_ub D n Hn



lemma seq_inj (s : Fin n → Fin D → Fin n) (sdef : seq_is_line D n (strengthen n Hn) s) :
  Set.InjOn s ↑(Finset.univ : Finset (Fin n)) :=
  by
  intro x _ y _ main
  rw [Function.funext_iff] at main
  have := sdef.non_pt
  rw [not_forall] at this
  obtain ⟨d,dp⟩ := this
  specialize main d
  cases' sdef.idc d with cst inc dec
  · exfalso ; exact dp cst
  · rw [inc, inc] at main
    exact main
  · rw [dec, dec] at main
    exact Opp_inj _ (strengthen n Hn) _ _ main



#exit

-- Both depend on classical choice, so making a constructive pairing strat would be mildly pointless for this project
#print axioms Finset.all_card_le_biUnion_card_iff_existsInjective'
#print axioms Fintype.all_card_le_rel_image_card_iff_exists_injective
