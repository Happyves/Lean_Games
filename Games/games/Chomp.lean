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








-- # Second attempt

#exit

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


def chain_nondomi : List (ℕ × ℕ) → Prop := List.Pairwise nondomi

lemma chain_nondomi_sub (l L :  List (ℕ × ℕ)) :
  chain_nondomi (l ++ L) → chain_nondomi l :=
  by
  induction' l with x l ih
  · intro _
    dsimp [chain_nondomi]
    apply List.Pairwise.nil
  · intro H
    dsimp [chain_nondomi] at *
    cases' H
    rename_i H1 H2
    apply List.Pairwise.cons
    · intro q ql
      apply H2
      exact List.mem_append.mpr (Or.inl ql)
    · exact ih H1


lemma chain_nondomi_sub' (l L :  List (ℕ × ℕ)) :
  chain_nondomi (l ++ L) → chain_nondomi L :=
  by
  induction' l with x l ih
  · intro h
    simp_rw [List.nil_append] at h
    exact h
  · intro H
    dsimp [chain_nondomi] at *
    cases' H
    rename_i H1 H2
    exact ih H1



structure Chomp_law (height length : ℕ) (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  h : act.2 ≤ height
  l : act.1 ≤ length
  nd : Chomp_state ini hist ≠ {(0,0)} → chain_nondomi (act :: hist)
  nz_act : act ≠ (0,0)
  nz_hist : (0,0) ∉ hist
  z_ini : (0,0) ∈ ini

def preChomp (height length : ℕ) : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := Comp_init height length
  win_states := (fun state => state = {(0,0)})
  transition := fun ini hist act => if Chomp_state ini hist ≠ {(0,0)}
                                    then {(0,0)}
                                    else (Chomp_state ini) (act :: hist)
  law := Chomp_law height length


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

lemma Chomp_state_zero (hist : List (ℕ × ℕ)) (hh : (0,0) ∉ hist): Chomp_state {(0,0)} hist = {(0,0)} :=
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


lemma Chomp_law_careless (h_base : 0 < height ∧ 0 < length) :
  careless (Chomp_law height length) (Chomp_law height length) (Chomp_state (preChomp height length).init_game_state []) (preChomp height length).law (preChomp height length).transition :=
  by
  intro ini hist prehist Hpre Hleg
  dsimp [preChomp]
  ext act
  constructor
  · intro c
    constructor
    · exact c.h
    · exact c.l
    · intro H
      split_ifs at H with q
      · rw [List.cons_head_tail, Chomp_state_blind] at H
        have := (c.nd H)
        rw [← List.cons_append] at this
        apply chain_nondomi_sub _ _ this
      · exfalso
        apply H
        apply Chomp_state_zero
        intro con
        apply c.nz_hist
        exact List.mem_append_left prehist con
    · exact c.nz_act
    · intro con
      apply c.nz_hist
      exact List.mem_append_left prehist con
    · split_ifs
      · rw [List.cons_head_tail]
        cases' prehist with x l
        · contradiction
        · cases' Hleg
          rename_i Q
          rw [ite_id] at Q



  · intro c
    constructor
    · exact c.h
    · exact c.l
    · intro H
      split_ifs at c with q
      · exfalso
        apply H
        rw [Finset.eq_singleton_iff_unique_mem]
        constructor
        · cases' prehist with x l
          · contradiction
          · cases' Hleg
            dsimp at q
            rename_i Q
            rw [ite_id] at Q
            rw [Chomp_state_has_zero_iff_hist_has_zero]
            · intro con
              rw [List.mem_append] at con
              cases' con with k k
              · exact c.nz_hist k
              · rw [List.mem_cons] at k
                cases' k with k k
                · exact Q.nz_act k.symm
                · exact Q.nz_hist k
            · have := Chomp_state_sub_ini ini l
              rw [q] at this
              apply this
              exact Finset.mem_singleton.mpr rfl


        · intro x xdef
          replace xdef := (Chomp_state_sub' ini _ _) xdef
          rw [← List.cons_head_tail _ Hpre, List.cons_eq_singleton_append ] at xdef
          replace xdef := (Chomp_state_sub' ini _ _) xdef
          rwa [q, Finset.mem_singleton] at xdef
      ·
















-- # First approach

#exit

-- pretty print the state
def pp_Chomp_state (l : List (ℕ × ℕ)) :=
  ((Finset.range (length)) ×ˢ (Finset.range (height))).filter
    (fun p => ∀ q ∈ l, nondomi q p)

--def play_condition (hist : List (ℕ × ℕ)) := ∃ x ∈ (List.range (length)) ×ˢ (List.range (height)), ∀ q ∈ hist, nondomi q x

def chain_nondomi : List (ℕ × ℕ) → Prop
| [] => True
| act :: hist => (chain_nondomi hist) ∧ (∀ q ∈ hist, nondomi q act)

lemma chain_nondomi_sub (l L :  List (ℕ × ℕ)) :
  chain_nondomi (l ++ L) → chain_nondomi l :=
  by
  induction' l with x l ih
  · intro _
    dsimp [chain_nondomi]
  · intro H
    dsimp [chain_nondomi] at *
    constructor
    · apply ih
      exact H.1
    · intro q ql
      apply H.2
      exact List.mem_append.mpr (Or.inl ql)



structure Chomp_law (_ : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  h : act.2 ≤ height
  l : act.1 ≤ length
  nd : pp_Chomp_state height length hist ≠ {(0,0)}  → chain_nondomi hist
  --nd : pp_Chomp_state height length hist ≠ {(0,0)}  → ∀ q ∈ hist, nondomi q act
  nz : act ≠ (0,0) -- even when end is reached, the partial function phenomenon forbids playing (0,0)
  -- for the game to be playable, one of `height` or `length` must be positive



def Chomp : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := (pp_Chomp_state height length) []
  win_states := (fun state => state = {(0,0)})
  transition := fun _ hist act => if pp_Chomp_state height length hist ≠ {(0,0)}
                                    then {(0,0)}
                                    else (pp_Chomp_state height length) (act :: hist)
  law := Chomp_law height length


lemma pp_Chomp_state_sub (l L :  List (ℕ × ℕ)) :
  pp_Chomp_state height length (l ++ L) ⊆ pp_Chomp_state height length l :=
  by
  intro x xdef
  dsimp [pp_Chomp_state] at *
  rw [Finset.mem_filter, Finset.mem_product] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact List.mem_append.mpr (Or.inl ql)



lemma pp_Chomp_state_terminal_iff (hist : List (ℕ × ℕ)) :
  pp_Chomp_state height length hist = {(0,0)} ↔
  (∀ q ∈ (Finset.range (length)) ×ˢ (Finset.range (height)), q ≠ (0,0) → ∃ p ∈ hist, domi p q) :=
  by
  constructor
  · intro c q qdef qnz
    by_contra! con
    have : q ∈ pp_Chomp_state height length hist :=
      by
      dsimp [pp_Chomp_state]
      rw [Finset.mem_filter]
      exact ⟨qdef, con⟩
    rw [c, Finset.mem_singleton] at this
    exact qnz this
  · intro c
    dsimp [pp_Chomp_state]


--#exit

lemma act_ne_zero_of_Chomp_law (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act now : ℕ × ℕ)
  (h : Chomp_law height length ini hist now) (ha : act ∈ hist) : act ≠ (0,0) :=
  by
  induction' hist with x l ih
  · contradiction
  · cases' ha with q
    · intro con


--#exit


lemma pp_Chomp_state_nonempty (h_base : 0 < height ∧ 0 < length) (l : List (ℕ × ℕ)) : pp_Chomp_state height length l ≠ ∅ :=
  by
  apply @Finset.ne_empty_of_mem _ (0,0) _
  dsimp [pp_Chomp_state]
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨h_base.2, h_base.1⟩
  · intro q ql
    dsimp [nondomi, domi]
    intro con
    rw [Nat.le_zero, Nat.le_zero] at con




lemma Chomp_law_careless (h_base : 0 < height ∧ 0 < length) :
  careless (Chomp_law height length) (Chomp_law height length) ((pp_Chomp_state height length) []) (Chomp height length).law (Chomp height length).transition :=
  by
  intro ini hist prehist Hpre Hleg
  dsimp [Chomp]
  ext act
  constructor
  · intro H
    constructor
    · exact H.h
    · exact H.l
    · intro hh
      apply chain_nondomi_sub hist prehist
      apply H.nd






#exit

def Chomp_measure (hist : List (ℕ × ℕ)) : ℕ :=
  (List.length (@pp_Chomp_state height length hist))


lemma warum : (@Chomp height length).init_game_state = (@pp_Chomp_state height length) [] := by rfl



lemma Chomp_measure_lb
  (f_strat s_strat : Strategy (List (ℕ × ℕ)) (ℕ × ℕ))
  (f_law : Strategy_legal (@Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal (@Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat s_strat)
  (turn : ℕ) :
  let H := History_on_turn (@Chomp height length).init_game_state f_strat s_strat
  1 ≤ (@Chomp_measure height length) (H turn) :=
  by
  intro H
  rw [Nat.one_le_iff_ne_zero]
  intro con
  rw [Chomp_measure, List.length_eq_zero, pp_Chomp_state, List.filter_eq_nil] at con
  specialize con (0,0) (by rw [List.mem_product] ; constructor <;> {rw [List.mem_range] ; apply Nat.zero_lt_succ})
  apply con
  apply decide_eq_true
  intro q qH
  rw [nondomi,domi]
  push_neg
  dsimp
  intro fz
  rw [Nat.le_zero] at fz
  by_contra! sz
  rw [Nat.le_zero] at sz
  have hmmm := (Chomp height length).mem_History_on_turn turn (pp_Chomp_state height length [])  f_strat s_strat f_law s_law q
  dsimp [H] at hmmm qH
  rw [warum] at qH
  rw [hmmm] at qH
  clear hmmm
  obtain ⟨t,_,no⟩ := qH
  dsimp [Strategy_legal, Chomp] at *
  specialize f_law t
  specialize s_law t
  replace f_law := f_law.nz
  replace s_law := s_law.nz
  cases' no with nof nos
  · apply f_law
    rw [← nof.right]
    rw [Prod.eq_iff_fst_eq_snd_eq]
    dsimp
    exact ⟨fz,sz⟩
  · apply s_law
    rw [← nos.right]
    rw [Prod.eq_iff_fst_eq_snd_eq]
    dsimp
    exact ⟨fz,sz⟩



lemma Chomp_measure_decrease
  (f_strat s_strat : Strategy (List (ℕ × ℕ)) (ℕ × ℕ))
  (f_law : Strategy_legal (Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal (Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat s_strat) :
  let H := History_on_turn (Chomp height length).init_game_state f_strat s_strat
  ∀ turn : ℕ, ((Chomp_measure height length) (H (turn + 1)) < (Chomp_measure height length) (H (turn))) ∨ ((@Chomp_measure height length) (H (turn +1)) ≤ 1) :=
  by
  intro H t
  rw [Chomp_measure, Chomp_measure]
  rw [or_iff_not_imp_right]
  intro non_base
  by_cases q : Turn_fst (t + 1)
  · dsimp [pp_Chomp_state, History_on_turn]
    rw [if_pos q]
    sorry
  · sorry




#exit


lemma Chomp_termination_pre
  (f_strat s_strat : Strategy (List (ℕ × ℕ)) (ℕ × ℕ))
  (f_law : Strategy_legal (@Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal (@Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat s_strat) :
  let H := History_on_turn (@Chomp height length).init_game_state f_strat s_strat
  ∃ turn : ℕ, (@Chomp_measure height length) (H turn) = 1 :=
  by
  intro H
  have : ∃ turn : ℕ, (@Chomp_measure height length) (H turn) - 1 = 0 :=
    by
    apply Nat.well_ordered
    intro n
    simp only [tsub_eq_zero_iff_le]
    rw [tsub_lt_tsub_iff_right]
    apply Chomp_measure_decrease height length f_strat s_strat f_law s_law
    apply Chomp_measure_lb height length f_strat s_strat f_law s_law (n+1)
  convert this using 2
  rename_i t
  rw [tsub_eq_zero_iff_le]
  have that := Chomp_measure_lb height length f_strat s_strat f_law s_law t
  rw [Nat.eq_iff_le_and_ge]
  constructor
  · intro a
    exact a.1
  · intro b
    exact ⟨b, that⟩


#exit
lemma Chomp_measure_lowest_iff
  (hg : 1 ≤ height ∨ 1 ≤ length)
  (f_strat s_strat : Strategy (List (ℕ × ℕ)) (ℕ × ℕ))
  (f_law : Strategy_legal (@Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal (@Chomp height length).init_game_state (fun _ => (@Chomp height length).law) f_strat s_strat s_strat)
  (turn : ℕ) :
  let H := History_on_turn (@Chomp height length).init_game_state f_strat s_strat
  (@Chomp_measure height length) (H turn) = 1 ↔ (@Chomp height length).win_states (H turn) :=
  by
  sorry
