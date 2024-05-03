/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.List
import Games.gameLib.Conditioning_Symm
import Mathlib.Tactic
import Mathlib.Data.List.ProdSigma




def domi (p q : ℕ × ℕ) : Prop := p.1 ≤ q.1 ∧ p.2 ≤ q.2

def nondomi (p q : ℕ × ℕ) : Prop := ¬ domi p q

instance : DecidableRel domi :=
  by
  intro p q
  rw [domi]
  exact And.decidable

instance : DecidableRel nondomi :=
  by
  intro p q
  rw [nondomi]
  exact Not.decidable

instance (l : List (ℕ × ℕ)) : DecidablePred (fun p => ∀ q ∈ l, nondomi q p) :=
  by
  intro p
  dsimp [nondomi,domi]
  exact List.decidableBAll (fun x => ¬(x.1 ≤ p.1 ∧ x.2 ≤ p.2)) l


def Chomp_state (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) :=
  ini.filter (fun p => ∀ q ∈ hist, nondomi q p)


lemma Chomp_state_sub (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) :
  Chomp_state ini (l ++ L) ⊆ Chomp_state ini l :=
  by
  intro x xdef
  dsimp [Chomp_state] at *
  rw [Finset.mem_filter] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact List.mem_append.mpr (Or.inl ql)

lemma Chomp_state_sub' (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) :
  Chomp_state ini (l ++ L) ⊆ Chomp_state ini L :=
  by
  intro x xdef
  dsimp [Chomp_state] at *
  rw [Finset.mem_filter] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact List.mem_append_right l ql


def Comp_init (height length : ℕ) := (Finset.range (length)) ×ˢ (Finset.range (height))

lemma Chomp_state_blind (ini : Finset (ℕ × ℕ)) (hist prehist : List (ℕ × ℕ)) :
  Chomp_state (Chomp_state ini prehist) hist = Chomp_state ini (hist ++ prehist) :=
  by
  ext x
  constructor
  · intro H
    dsimp [Chomp_state] at *
    simp_rw [Finset.mem_filter] at *
    constructor
    · exact H.1.1
    · intro q qq
      rw [List.mem_append] at qq
      cases' qq with k k
      · exact H.2 q k
      · exact H.1.2 q k
  · intro H
    dsimp [Chomp_state] at *
    simp_rw [Finset.mem_filter] at *
    constructor
    · constructor
      · exact H.1
      · intro q qh
        apply H.2
        exact List.mem_append_right hist qh
    · intro q qh
      apply H.2
      exact List.mem_append.mpr (Or.inl qh)


structure Chomp_law (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  act_mem : act ∈ ini
  nd : ∀ q ∈ hist, nondomi q act
  nz_act : act ≠ (0,0)


def preChomp (height length : ℕ) : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := Comp_init height length
  win_states := (fun state => state = {(0,0)})
  transition := fun ini hist act => if Chomp_state ini hist ≠ {(0,0)}
                                    then (Chomp_state ini) (act :: hist)
                                    else {(0,0)}
  law := fun ini hist act => if Chomp_state ini hist ≠ {(0,0)}
                             then Chomp_law ini hist act
                             else act ≠ (0,0) -- saves ass in `preChomp_law_careless`



lemma Chomp_state_ini_zero (hist : List (ℕ × ℕ)) (hh : (0,0) ∉ hist): Chomp_state {(0,0)} hist = {(0,0)} :=
  by
  dsimp [Chomp_state]
  rw [Finset.filter_eq_self]
  intro x xdef q qh
  rw [Finset.mem_singleton] at xdef
  rw [xdef]
  dsimp [nondomi, domi]
  intro con
  simp_rw [Nat.le_zero] at con
  apply hh
  convert qh
  · exact con.1.symm
  · exact con.2.symm

lemma Chomp_state_has_zero_iff_hist_has_zero
  (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (hist : List (ℕ × ℕ)) :
  (0,0) ∈ Chomp_state ini hist ↔ (0,0) ∉ hist :=
  by
  constructor
  · intro c
    dsimp [Chomp_state] at c
    rw [Finset.mem_filter] at c
    dsimp [nondomi, domi] at c
    intro con
    apply c.2 _ con
    decide
  · intro c
    dsimp [Chomp_state]
    rw [Finset.mem_filter]
    constructor
    · exact hini
    · intro q qh
      dsimp [nondomi, domi]
      intro con
      simp_all only [nonpos_iff_eq_zero]
      unhygienic with_reducible aesop_destruct_products
      simp_all only

lemma Chomp_state_sub_ini (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) :
  Chomp_state ini hist ⊆ ini := by dsimp [Chomp_state]; exact Finset.filter_subset (fun p => ∀ q ∈ hist, nondomi q p) ini

lemma Chomp_state_hist_zero (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (main : (0,0) ∈ hist) :
  Chomp_state ini hist = ∅ :=
  by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x xdef
  dsimp [Chomp_state] at xdef
  rw [Finset.mem_filter] at xdef
  apply xdef.2 _ main
  dsimp [domi]
  simp_all only [Prod.forall, zero_le, and_self]


lemma Chomp_state_state_empty (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (hist : List (ℕ × ℕ)) (main : Chomp_state ini hist = ∅) :
  (0,0) ∈ hist :=
  by
  dsimp [Chomp_state] at main
  simp_rw [Finset.eq_empty_iff_forall_not_mem, Finset.mem_filter] at main
  dsimp [nondomi, domi] at main
  push_neg at main
  specialize main _ hini
  obtain ⟨q, qh, qz1, qz2⟩ := main
  simp only [nonpos_iff_eq_zero] at *
  convert qh <;> {rw [eq_comm] ; assumption}





lemma preChomp_law_careless (height length : ℕ) :
  careless (preChomp height length).law (preChomp height length).law (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).transition :=
  by
  intro ini hist prehist pHne pHl
  ext act
  constructor
  · intro c
    dsimp [preChomp] at c
    by_cases q1 : Chomp_state ini (hist ++ prehist) ≠ {(0,0)}
    · rw [if_pos q1] at c
      by_cases q2 : Chomp_state (Symm_Game_World.transition (preChomp height length) ini (List.tail prehist) (List.head prehist pHne)) (hist) ≠ {(0,0)}
      · dsimp [preChomp] at *
        rw [if_pos q2]
        rw [List.cons_head_tail] at *
        by_cases q3 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
        · rw [if_pos q3] at *
          constructor
          · dsimp [Chomp_state]
            rw [Finset.mem_filter]
            constructor
            · exact c.act_mem
            · intro e eh
              apply c.nd
              exact List.mem_append_right hist eh
          · intro e eh
            apply c.nd
            exact List.mem_append_left prehist eh
          · apply c.nz_act
        · rw [if_neg q3] at *
          exfalso
          have : Chomp_state {(0, 0)} hist ⊂ {(0, 0)} :=
            by
            rw [Finset.ssubset_iff_subset_ne]
            constructor
            · apply Chomp_state_sub_ini
            · exact q2
          rw [Finset.ssubset_singleton_iff] at this
          have that := Chomp_state_has_zero_iff_hist_has_zero {(0,0)} (by apply Finset.mem_singleton_self) hist
          rw [iff_not_comm] at that
          rw [this] at that
          simp only [Finset.not_mem_empty, not_false_eq_true, iff_true] at that
          have thut := c.nd (0,0) (by exact List.mem_append_left prehist that)
          dsimp [nondomi, domi] at thut
          apply thut
          simp only [zero_le, and_self]
      · dsimp [preChomp] at *
        rw [if_neg q2]
        apply c.nz_act
    · rw [if_neg q1] at c
      by_cases q2 : Chomp_state (Symm_Game_World.transition (preChomp height length) ini (List.tail prehist) (List.head prehist pHne)) (hist) ≠ {(0,0)}
      · dsimp [preChomp] at *
        rw [if_pos q2]
        rw [not_not] at q1
        rw [List.cons_head_tail] at *
        by_cases q3 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
        · rw [if_pos q3] at *
          exfalso
          rw [Chomp_state_blind] at q2
          exact q2 q1
        · rw [if_neg q3] at *
          exfalso
          have : Chomp_state {(0, 0)} hist ⊂ {(0, 0)} :=
            by
            rw [Finset.ssubset_iff_subset_ne]
            constructor
            · apply Chomp_state_sub_ini
            · exact q2
          rw [Finset.ssubset_singleton_iff] at this
          have that := Chomp_state_has_zero_iff_hist_has_zero {(0,0)} (by apply Finset.mem_singleton_self) hist
          rw [iff_not_comm] at that
          rw [this] at that
          simp only [Finset.not_mem_empty, not_false_eq_true, iff_true] at that
          have thut : (0,0) ∈ ini :=
            by
            have := Chomp_state_sub_ini ini (hist ++ prehist)
            rw [q1] at this
            apply this (Finset.mem_singleton_self (0,0))
          have thus := Chomp_state_has_zero_iff_hist_has_zero ini thut (hist ++ prehist)
          rw [q1] at thus
          simp only [Finset.mem_singleton, List.mem_append, true_iff] at thus
          apply thus
          left
          exact that
      · dsimp [preChomp] at *
        rw [if_neg q2]
        apply c
  · intro c
    dsimp [preChomp] at *
    rw [List.cons_head_tail] at *
    by_cases q1 : Chomp_state ini (hist ++ prehist) ≠ {(0,0)}
    · rw [if_pos q1]
      by_cases q2 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
      · rw [if_pos q2] at c
        by_cases q3 : Chomp_state (Chomp_state ini prehist) hist ≠ {(0, 0)}
        · rw [if_pos q3] at c
          constructor
          · apply Chomp_state_sub_ini
            apply c.act_mem
          · have := c.act_mem
            dsimp [Chomp_state] at this
            rw [Finset.mem_filter] at this
            intro e eh
            rw [List.mem_append] at eh
            · cases' eh with k k
              · exact c.nd e k
              · exact this.2 e k
          · exact c.nz_act
        · rw [if_neg q3] at c
          rw [not_not] at q3
          exfalso
          rw [Chomp_state_blind] at q3
          exact q1 q3
      · rw [if_neg q2] at c
        by_cases q3 : Chomp_state {(0, 0)} hist ≠ {(0, 0)}
        · rw [if_pos q3] at c
          exfalso
          apply c.nz_act
          have := c.act_mem
          rwa [Finset.mem_singleton] at this
        · rw [if_neg q3] at c
          rw [not_not] at q3 q2
          exfalso
          have : (0,0) ∉ hist :=
            by
            intro con
            have := Chomp_state_hist_zero {(0,0)} hist con
            rw [this] at q3
            contradiction
          have temp : hist ++ prehist = (hist ++ [prehist.head pHne]) ++ prehist.tail :=
            by rw [List.append_assoc, List.singleton_append, List.cons_head_tail]
          rw [temp] at q1
          have that := Chomp_state_sub' ini (hist ++ [prehist.head pHne]) prehist.tail
          rw [q2] at that
          rw [Finset.subset_singleton_iff] at that
          cases' that with k k
          · have fact : (0,0) ∈ ini :=
              by
              apply Chomp_state_sub_ini _ prehist.tail
              rw [q2]
              exact Finset.mem_singleton.mpr rfl
            have more := Chomp_state_state_empty _ fact _ k
            have thut : (0,0) ∉ prehist.tail :=
              by
              intro con
              have tmp := Chomp_state_hist_zero ini _ con
              rw [tmp] at q2
              contradiction
            rw [List.mem_append] at more
            cases' more with more more
            · rw [List.mem_append] at more
              cases' more with more more
              · exact this more
              · rw [List.mem_singleton] at more
                cases' prehist with x l
                · contradiction
                · cases' pHl
                  · rename_i uno dos
                    by_cases last : Turn_fst (List.length l + 1)
                    · rw [if_pos last, if_neg (by rw [not_not] ; apply q2)] at dos
                      apply dos
                      rw [more]
                      rfl
                    · rw [if_neg last, if_neg (by rw [not_not] ; apply q2)] at dos
                      apply dos
                      rw [more]
                      rfl
            · exact thut more
          · exact q1 k
    · rw [if_neg q1]
      split_ifs at c
      · exact c
      · apply c.nz_act
      · exact c
      · apply c.nz_act





lemma preChomp_tranistion_careless (height length : ℕ) :
  careless (preChomp height length).law (preChomp height length).law (preChomp height length).init_game_state (preChomp height length).transition (preChomp height length).transition :=
  by
  intro ini hist prehist pHne pHl
  funext act
  dsimp [preChomp]
  by_cases q1 : Chomp_state ini (hist ++ prehist) ≠ {(0,0)}
  · rw [if_pos q1] at *
    by_cases q2 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
    · simp_rw [if_pos q2, List.cons_head_tail, Chomp_state_blind] at *
      rw [if_pos q1, List.cons_append]
    · simp_rw [if_neg q2] at *
      by_cases q3 : Chomp_state {(0, 0)} hist ≠ {(0, 0)}
      · rw [if_pos q3]
        have : Chomp_state {(0, 0)} hist ⊂ {(0, 0)} :=
            by
            rw [Finset.ssubset_iff_subset_ne]
            constructor
            · apply Chomp_state_sub_ini
            · exact q3
        rw [Finset.ssubset_singleton_iff] at this
        have that := Chomp_state_has_zero_iff_hist_has_zero {(0,0)} (by apply Finset.mem_singleton_self) hist
        rw [iff_not_comm] at that
        rw [this] at that
        simp only [Finset.not_mem_empty, not_false_eq_true, iff_true] at that
        have thut_l : (0,0) ∈ act :: (hist ++ prehist) :=
          by apply List.mem_cons_of_mem ; apply List.mem_append_left ; exact that
        rw [Chomp_state_hist_zero _ _ thut_l]
        have thut_r : (0,0) ∈ act :: (hist) :=
          by apply List.mem_cons_of_mem ; exact that
        rw [Chomp_state_hist_zero _ _ thut_r]
      · rw [if_neg q3, not_not] at *
        -- fix carelessness
