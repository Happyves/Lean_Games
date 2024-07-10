/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.List
import Games.gameLib.Conditioning_Symm
import Mathlib.Tactic
import Mathlib.Data.List.ProdSigma
import Games.gameLib.Stealing_Symm




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

lemma Chomp_state_sub_cons (ini : Finset (ℕ × ℕ)) (x : ℕ × ℕ) (l :  List (ℕ × ℕ)) :
  Chomp_state ini (x :: l) ⊆ Chomp_state ini l :=
  by
  rw [List.cons_eq_singleton_append]
  apply Chomp_state_sub'


lemma Chomp_state_sub_of_hist_sub (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) (h : l ⊆ L) :
  Chomp_state ini (L) ⊆ Chomp_state ini l :=
  by
  intro x xdef
  dsimp [Chomp_state] at *
  rw [Finset.mem_filter] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact h ql



def Chomp_init (height length : ℕ) := (Finset.range (length+1)) ×ˢ (Finset.range (height+1))

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
  hist_mem : ∀ q ∈ hist, q ∈ ini
  hist_nd : List.Pairwise (fun x y => nondomi y x) hist
  nd : ∀ q ∈ hist, nondomi q act
  nz_act : act ≠ (0,0)


def preChomp (height length : ℕ) : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := Chomp_init height length
  win_states := (fun state => state = {(0,0)})
  transition := fun ini hist act => if Chomp_state ini hist ≠ {(0,0)}
                                    then (Chomp_state ini) (act :: hist)
                                    else {(0,0)}
  law := fun ini hist act => if (0,0) ∈ ini ∧ (0,0) ∉ hist
                             then
                              if Chomp_state ini hist ≠ {(0,0)}
                              then Chomp_law ini hist act
                              else act ≠ (0,0) -- saves ass in `preChomp_law_careless`
                             else True

--#exit

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



lemma Chomp_law_state_mem (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) (leg : Chomp_law ini hist act) :
  act ∈ Chomp_state ini hist :=
  by
  dsimp [Chomp_state]
  rw [Finset.mem_filter]
  constructor
  · exact leg.act_mem
  · exact leg.nd


lemma Chomp_law_sub (ini : Finset (ℕ × ℕ) ) (l L : List (ℕ × ℕ)) (act : ℕ × ℕ) (leg : Chomp_law ini (l ++ L) act) :
  Chomp_law ini L act :=
  by
  refine' ⟨leg.act_mem, _, _,  _ , leg.nz_act⟩
  · intro q qdef
    apply leg.hist_mem
    exact List.mem_append_right l qdef
  · have := leg.hist_nd
    rw [List.pairwise_append] at this
    exact this.2.1
  · intro q qdef
    apply leg.nd
    exact List.mem_append_right l qdef




lemma Chomp_hist_no_zero_of_Hist_legal (height length : ℕ) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (prehist : List (ℕ × ℕ))
  (main : Hist_legal (preChomp height length).law (preChomp height length).law ini prehist) : (0,0) ∉ prehist :=
  by
  induction' prehist with x l ih
  · decide
  · cases' main
    rename_i sofar now
    apply List.not_mem_cons_of_ne_of_not_mem
    · split_ifs at now
      all_goals { dsimp [preChomp] at now
                  rw [if_pos ⟨hini, ih sofar⟩ ] at now
                  split_ifs at now
                  · contrapose! now
                    apply now.symm
                  · rw [ne_comm]
                    apply now.nz_act}
    · exact ih sofar



lemma nondomi_zero (act : ℕ × ℕ) : nondomi act (0,0) ↔ act ≠ (0,0) := by
  dsimp [nondomi,domi]
  simp_rw [Nat.le_zero]
  simp_all only [not_and]
  unhygienic with_reducible aesop_destruct_products
  simp_all only [Prod.mk.injEq, not_and]



lemma Chomp_state_zero_act_non_zero (ini : Finset (ℕ × ℕ)) (hini : (0, 0) ∈ ini) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ)
  (hs : Chomp_state ini hist = {(0,0)}) (ha : act ≠ (0,0)) : Chomp_state ini (act :: hist) = {(0,0)} :=
  by
  dsimp [Chomp_state] at *
  have : (fun p => ∀ q ∈ act :: hist, nondomi q p) = (fun p => (nondomi act p) ∧ (∀ q ∈ hist, nondomi q p)) :=
    by
    ext p
    simp_all only [Prod.forall, List.mem_cons, forall_eq_or_imp]
    unhygienic with_reducible aesop_destruct_products
    simp_all only [Prod.forall, Prod.mk.injEq, not_and]
    apply Iff.intro
    · intro a
      simp_all only [Prod.forall, and_self, true_or, or_true, implies_true, forall_const]
    · intro a a_1 b a_2
      unhygienic with_reducible aesop_destruct_products
      unhygienic aesop_cases a_2
      · simp_all only [Prod.forall]
      · simp_all only [Prod.forall]
  simp_rw [this, Finset.filter_and,hs]
  rw [Finset.inter_eq_right]
  intro y ydef
  rw [Finset.mem_singleton] at ydef
  rw [ydef, Finset.mem_filter]
  exact ⟨ hini, (by rw [nondomi_zero]; exact ha)⟩

lemma Chomp_hist_mem_ini_of_Hist_legal (height length : ℕ) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (prehist : List (ℕ × ℕ))
  (main : Hist_legal (preChomp height length).law (preChomp height length).law ini prehist)
  (main' : Chomp_state ini prehist.tail ≠ {(0,0)}): ∀ q ∈ prehist, q ∈ ini :=
  by
  cases' prehist with x l
  · intro q no ; contradiction
  · intro q qdef
    rw [List.tail_cons] at main'
    cases' main
    rename_i sofar now
    rw [ite_self] at now
    rw [List.mem_cons] at qdef
    cases' qdef with qdef qdef
    · rw [qdef]
      dsimp [preChomp] at now
      rw [if_pos ⟨hini, Chomp_hist_no_zero_of_Hist_legal height length ini hini l sofar⟩ ] at now
      rw [if_pos main'] at now
      exact now.act_mem
    · dsimp [preChomp] at now
      rw [if_pos ⟨hini, Chomp_hist_no_zero_of_Hist_legal height length ini hini l sofar⟩ ] at now
      rw [if_pos main'] at now
      exact now.hist_mem _ qdef



--#exit

lemma Chomp_law_blind (ini : Finset (ℕ × ℕ) ) (l L : List (ℕ × ℕ)) (act : ℕ × ℕ) (c : Chomp_law ini (l ++ L) act) :
  Chomp_law (Chomp_state ini L) l act :=
  by
  constructor
  · dsimp [Chomp_state]
    rw [Finset.mem_filter]
    constructor
    · exact c.act_mem
    · intro e eh
      apply c.nd
      exact List.mem_append_right l eh
  · intro q qdef
    dsimp [Chomp_state]
    rw [Finset.mem_filter]
    constructor
    · exact c.hist_mem q (by exact List.mem_append.mpr (Or.inl qdef))
    · intro e eh
      have := c.hist_nd
      rw [List.pairwise_append] at this
      apply this.2.2
      · exact qdef
      · exact eh
  · have := c.hist_nd
    rw [List.pairwise_append] at this
    exact this.1
  · intro e eh
    apply c.nd
    exact List.mem_append_left L eh
  · apply c.nz_act



lemma Chomp_hist_pairwise_nondomi_of_Hist_legal (height length : ℕ) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (prehist : List (ℕ × ℕ))
  (main : Hist_legal (preChomp height length).law (preChomp height length).law ini prehist)
  (main' : Chomp_state ini prehist.tail ≠ {(0,0)}) : List.Pairwise (fun x y => nondomi y x) prehist :=
  by
  cases' prehist with x l
  · apply List.Pairwise.nil
  · cases' main
    rename_i sofar now
    rw [ite_self] at now
    dsimp [preChomp] at now
    rw [if_pos ⟨hini, Chomp_hist_no_zero_of_Hist_legal height length ini hini l sofar⟩ ] at now
    rw [List.tail_cons] at main'
    rw [ if_pos main'] at now
    apply List.Pairwise.cons
    · exact now.nd
    · exact now.hist_nd


--#exit

lemma Chomp_law_blind' (height length : Nat) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (l L : List (ℕ × ℕ)) (act : ℕ × ℕ)
  (leg : Hist_legal (preChomp height length).law (preChomp height length).law ini L) (c : Chomp_law (Chomp_state ini L) l act) :
  Chomp_law ini (l ++ L) act  :=
  by
  constructor
  · apply Chomp_state_sub_ini _ _ c.act_mem
  · intro q qdef
    have := c.hist_mem
    specialize this q
    dsimp [Chomp_state] at this
    rw [Finset.mem_filter] at this
    rw [List.mem_append] at qdef
    cases' qdef with qdef qdef
    · exact (this qdef).1
    · cases' L with x L
      · contradiction
      · have that : Chomp_state ini (x :: L).tail ≠ {(0,0)} :=
          by
          intro con
          cases' leg
          rename_i sofar now
          rw [ite_self] at now
          dsimp [preChomp] at now
          rw [if_pos ⟨hini, Chomp_hist_no_zero_of_Hist_legal height length ini hini L sofar⟩] at now
          rw [if_neg (by rw [not_not] ; apply con)] at now
          have fact := Chomp_state_zero_act_non_zero ini hini L x con now
          rw [fact] at c
          apply c.nz_act
          replace c := c.act_mem
          rw [Finset.mem_singleton] at c
          exact c
        exact Chomp_hist_mem_ini_of_Hist_legal height length ini hini (x :: L) leg that q qdef
  · rw [List.pairwise_append]
    constructor
    · apply c.hist_nd
    · constructor
      · cases' L with x L
        · apply List.Pairwise.nil
        · have that : Chomp_state ini (x :: L).tail ≠ {(0,0)} :=
            by
            intro con
            cases' leg
            rename_i sofar now
            rw [ite_self] at now
            dsimp [preChomp] at now
            rw [if_pos ⟨hini, Chomp_hist_no_zero_of_Hist_legal height length ini hini L sofar⟩] at now
            rw [if_neg (by rw [not_not] ; apply con)] at now
            have fact := Chomp_state_zero_act_non_zero ini hini L x con now
            rw [fact] at c
            apply c.nz_act
            replace c := c.act_mem
            rw [Finset.mem_singleton] at c
            exact c
          exact Chomp_hist_pairwise_nondomi_of_Hist_legal height length ini hini (x :: L) leg that
      · intro a al b bL
        replace c := c.hist_mem a al
        dsimp [Chomp_state] at c
        rw [Finset.mem_filter] at c
        exact c.2 b bL
  · intro q qdef
    rw [List.mem_append] at qdef
    cases' qdef with qdef qdef
    · apply c.nd q qdef
    · replace c := c.act_mem
      dsimp [Chomp_state] at c
      rw [Finset.mem_filter] at c
      exact c.2 q qdef
  · exact c.nz_act



lemma preChomp_law_careless (height length : ℕ) :
  careless (preChomp height length).law (preChomp height length).law (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).transition :=
  by
  intro ini hist prehist pHne pHl
  ext act
  by_cases fix : (0,0) ∈ ini ∧ (0, 0) ∉ hist
  · constructor
    · intro c
      dsimp [preChomp] at c
      rw [if_pos ⟨fix.1, (by apply List.not_mem_append fix.2 ; exact Chomp_hist_no_zero_of_Hist_legal height length ini fix.1 prehist pHl)⟩ ] at c
      by_cases q1 : Chomp_state ini (hist ++ prehist) ≠ {(0,0)}
      · rw [if_pos q1] at c
        by_cases q2 : Chomp_state (Symm_Game_World.transition (preChomp height length) ini (List.tail prehist) (List.head prehist pHne)) (hist) ≠ {(0,0)}
        · dsimp [preChomp] at *
          rw [if_pos q2]
          rw [List.cons_head_tail] at *
          by_cases q3 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
          · rw [if_pos q3] at *
            split_ifs
            all_goals { apply Chomp_law_blind _ _ _ _ c
            }
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
          split_ifs
          all_goals apply c.nz_act
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
          split_ifs
          all_goals apply c
    · intro c
      dsimp [preChomp] at *
      rw [if_pos ⟨fix.1, (by apply List.not_mem_append fix.2 ; exact Chomp_hist_no_zero_of_Hist_legal height length ini fix.1 prehist pHl)⟩ ]
      rw [List.cons_head_tail] at *
      by_cases q1 : Chomp_state ini (hist ++ prehist) ≠ {(0,0)}
      · rw [if_pos q1]
        by_cases q2 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
        · rw [if_pos q2] at c
          by_cases q3 : Chomp_state (Chomp_state ini prehist) hist ≠ {(0, 0)}
          · rw [if_pos q3] at c
            rw [if_pos ⟨(Chomp_state_has_zero_iff_hist_has_zero ini fix.1 prehist).mpr (Chomp_hist_no_zero_of_Hist_legal height length ini fix.1 prehist pHl) , fix.2⟩ ] at c
            exact Chomp_law_blind' height length _ fix.1 _ _ _ pHl c
          · rw [if_neg q3] at c
            rw [not_not] at q3
            exfalso
            rw [Chomp_state_blind] at q3
            exact q1 q3
        · rw [if_neg q2] at c
          by_cases q3 : Chomp_state {(0, 0)} hist ≠ {(0, 0)}
          · rw [if_pos q3, if_pos ⟨ (by apply Finset.mem_singleton_self) , fix.2⟩ ] at c
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
                      · rw [if_pos last, if_pos ⟨fix.1 , thut⟩ , if_neg (by rw [not_not] ; apply q2)] at dos
                        apply dos
                        rw [more]
                        rfl
                      · rw [if_neg last, if_pos  ⟨fix.1 , thut⟩, if_neg (by rw [not_not] ; apply q2)] at dos
                        apply dos
                        rw [more]
                        rfl
              · exact thut more
            · exact q1 k
      · rw [if_neg q1]
        split_ifs at c
        · exact c
        · apply c.nz_act
        · rename_i no
          push_neg at no
          exact False.elim (fix.2 (no (by apply Finset.mem_singleton_self)))
        · exact c
        · apply c.nz_act
        · exfalso
          rename_i no
          apply no
          rw [Chomp_state_has_zero_iff_hist_has_zero ini fix.1 prehist]
          exact ⟨Chomp_hist_no_zero_of_Hist_legal height length ini fix.1 prehist pHl, fix.2⟩
  · dsimp [preChomp]
    rw [if_neg (by push_neg at * ;intro _ ; simp_all only [ne_eq, forall_true_left, List.mem_append, true_or] )]
    simp only [ite_not, true_iff]
    split_ifs
    · rename_i a b c
      rw [← a] at b
      exact False.elim (by apply fix ; constructor ; apply Chomp_state_sub_ini ; apply b.1 ; apply b.2)
    · rename_i a b c
      rw [← a] at b
      exact False.elim (by apply fix ; constructor ; apply Chomp_state_sub_ini ; apply b.1 ; apply b.2)
    · rename_i a b c
      exact False.elim (by apply fix ; constructor ; apply Chomp_state_sub_ini ; apply b.1 ; apply b.2)
    · rename_i a b c
      exact False.elim (by apply fix ; constructor ; apply Chomp_state_sub_ini ; apply b.1 ; apply b.2)


--#exit


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
          simp_rw [List.mem_append] at more
          cases' more with more more
          · cases' more with more more
            · exact this more
            · rw [List.mem_singleton] at more
              cases' prehist with x l
              · contradiction
              · dsimp at *
                cases' pHl
                rename_i main
                split_ifs at main
                all_goals {dsimp [preChomp] at main ; rw [if_pos ⟨fact, thut⟩, if_neg (by rw [not_not] ; exact q2)] at main ; exact main more.symm}
          · exact thut more
        · exact q1 k
  · rw [if_neg q1] at *
    by_cases q2 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
    · simp_rw [if_pos q2, List.cons_head_tail, Chomp_state_blind] at *
      rw [if_neg q1]
    · simp_rw [if_neg q2] at *
      by_cases q3 : Chomp_state {(0, 0)} hist ≠ {(0, 0)}
      · exfalso
        rw [not_not] at *
        apply q3
        apply Chomp_state_ini_zero hist
        intro con
        have := Chomp_state_hist_zero ini _ con
        have that := Chomp_state_sub ini hist prehist
        simp_all only [ne_eq, Finset.singleton_subset_iff, Finset.not_mem_empty]
      · rw [not_not] at *
        rw [if_neg (by rw [not_not] ; exact q3)]




lemma Chomp_init_has_zero (height length : ℕ)  : (0,0) ∈ Chomp_init height length :=
  by
  dsimp [Chomp_init]
  simp_rw [Finset.mem_product, Finset.mem_range, and_comm]
  constructor <;> {exact Nat.add_pos_right _ Nat.le.refl}




lemma preChomp_coherent (height length : ℕ)  : (preChomp height length).coherent_end :=
  by
  intro f_strat s_strat f_leg s_leg t main
  dsimp [preChomp] at *
  by_cases q1 : Turn_fst (t + 1)
  · rw [Symm_Game_World.state_on_turn_fst_to_snd _ _ _ _ q1]
    dsimp [preChomp]
    rw [if_neg]
    rw [not_not]
    cases' t with t
    · dsimp [Symm_Game_World.state_on_turn, Symm_Game_World.history_on_turn, History_on_turn] at *
      simp_all only [zero_add]
      rfl
    · dsimp [Symm_Game_World.state_on_turn, Symm_Game_World.history_on_turn, History_on_turn] at main
      rw [if_neg (by contrapose q1 ; rw [not_not] at q1 ; rw [← Turn_fst_not_step] ; exact q1)] at main
      split_ifs at main with k
      · dsimp [History_on_turn]
        split_ifs with tu
        · have : f_strat (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) ≠ (0, 0) :=
            by
            specialize f_leg t tu
            by_cases split_ifs_is_wierd : ¬Chomp_state (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) = {(0, 0)}
            · rw [if_pos ⟨(Chomp_init_has_zero _ _), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩ , if_pos (split_ifs_is_wierd)] at f_leg
              exact f_leg.nz_act
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_neg (split_ifs_is_wierd)] at f_leg
              exact f_leg
          apply Chomp_state_zero_act_non_zero
          · exact Chomp_init_has_zero _ _
          · exact k
          · exact this
        · have : s_strat (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) ≠ (0, 0) :=
            by
            specialize s_leg t tu
            by_cases split_ifs_is_wierd : ¬Chomp_state (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) = {(0, 0)}
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_pos (split_ifs_is_wierd)] at s_leg
              exact s_leg.nz_act
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_neg (split_ifs_is_wierd)] at s_leg
              exact s_leg
          apply Chomp_state_zero_act_non_zero
          · exact Chomp_init_has_zero _ _
          · exact k
          · exact this
      · dsimp [History_on_turn]
        rw [if_neg (by rw [Turn_fst_not_step, not_not] ; exact q1)]
        exact main
  · rw [Turn_not_fst_iff_snd] at q1
    rw [Symm_Game_World.state_on_turn_snd_to_fst _ _ _ _ q1]
    dsimp [preChomp]
    rw [if_neg]
    rw [not_not]
    cases' t with t
    · dsimp [Symm_Game_World.state_on_turn, Symm_Game_World.history_on_turn, History_on_turn] at *
      simp_all only [zero_add]
      rfl
    · dsimp [Symm_Game_World.state_on_turn, Symm_Game_World.history_on_turn, History_on_turn] at main
      rw [if_pos (by contrapose q1 ; rw [← Turn_snd_not_step, ← Turn_not_fst_iff_snd] ; exact q1)] at main
      split_ifs at main with k
      · dsimp [History_on_turn]
        split_ifs with tu
        · have : f_strat (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) ≠ (0, 0) :=
            by
            specialize f_leg t tu
            by_cases split_ifs_is_wierd : ¬Chomp_state (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) = {(0, 0)}
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_pos (split_ifs_is_wierd)] at f_leg
              exact f_leg.nz_act
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_neg (split_ifs_is_wierd)] at f_leg
              exact f_leg
          apply Chomp_state_zero_act_non_zero
          · exact Chomp_init_has_zero _ _
          · exact k
          · exact this
        · have : s_strat (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) ≠ (0, 0) :=
            by
            specialize s_leg t tu
            by_cases split_ifs_is_wierd : ¬Chomp_state (Chomp_init height length) (History_on_turn (Chomp_init height length) f_strat s_strat t) = {(0, 0)}
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_pos (split_ifs_is_wierd)] at s_leg
              exact s_leg.nz_act
            · rw [if_pos ⟨(Chomp_init_has_zero _ _ ), (by rw [← Chomp_state_has_zero_iff_hist_has_zero (Chomp_init height length) (Chomp_init_has_zero _ _ ), k] ; apply Finset.mem_singleton_self )⟩, if_neg (split_ifs_is_wierd)] at s_leg
              exact s_leg
          apply Chomp_state_zero_act_non_zero
          · exact Chomp_init_has_zero _ _
          · exact k
          · exact this
      · dsimp [History_on_turn]
        rw [if_pos (by rw [Turn_fst_not_step] ; exact q1)]
        exact main


lemma preChomp_playable (height length : ℕ) : (preChomp height length).playable :=
  by
  intro ini hist hist_leg
  dsimp [preChomp]
  by_cases q : ¬Chomp_state ini hist = {(0, 0)}
  · simp_rw [if_pos q]
    split_ifs
    · have : ∃ act, act ∈ Chomp_state ini hist ∧ act ≠ (0,0) :=
        by
        contrapose! q
        ext x
        constructor
        · intro xdef
          specialize q x xdef
          rename_i h
          aesop_subst q
          simp_all only [gt_iff_lt, Finset.mem_singleton]
        · intro xdef
          rw [Finset.mem_singleton] at xdef
          rw [xdef]
          dsimp [Chomp_state]
          rw [Finset.mem_filter]
          rename_i gain
          refine' ⟨gain.1, _ ⟩
          intro q qdef
          dsimp [nondomi, domi]
          intro con
          simp_rw [Nat.le_zero] at con
          apply gain.2
          convert qdef
          · exact con.1.symm
          · exact con.2.symm
      obtain ⟨act, act_mem, act_nz⟩ := this
      use act
      constructor
      · exact (Chomp_state_sub_ini _ _) act_mem
      · rename_i facts
        apply Chomp_hist_mem_ini_of_Hist_legal height length _ facts.1 _ hist_leg
        contrapose! q
        cases' hist with x l
        · apply q
        · apply Chomp_state_zero_act_non_zero _ facts.1 l x q
          intro con
          rw [con] at facts
          apply facts.2
          exact List.mem_cons_self (0, 0) l
      · rename_i facts
        apply Chomp_hist_pairwise_nondomi_of_Hist_legal height length _ facts.1 _ hist_leg
        contrapose! q
        cases' hist with x l
        · apply q
        · apply Chomp_state_zero_act_non_zero _ facts.1 l x q
          intro con
          rw [con] at facts
          apply facts.2
          exact List.mem_cons_self (0, 0) l
      · dsimp [Chomp_state] at act_mem
        rw [Finset.mem_filter] at act_mem
        exact act_mem.2
      · exact act_nz
    · use (0,0)
  · simp_rw [if_neg q]
    use (1,0)
    split_ifs
    · decide

--#exit

def Chomp (height length : ℕ) : zSymm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  toSymm_Game_World := preChomp height length
  law_careless := preChomp_law_careless height length
  transition_careless := preChomp_tranistion_careless height length
  coherent := preChomp_coherent height length
  playable := preChomp_playable height length



lemma Chomp_state_ini_not_zero (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0)  : ¬Chomp_state (Chomp_init height length) [] = {(0, 0)} :=
  by
  dsimp [Chomp_state, Chomp_init]
  apply ne_of_not_subset
  intro con
  specialize @con (length, height)
    (by rw [Finset.mem_filter ]
        constructor
        · simp_rw [Finset.mem_product, Finset.mem_range]
          constructor <;> {exact Nat.le.refl}
        · intro q no ; contradiction)
  simp only [Finset.mem_singleton, Prod.mk.injEq] at con
  cases' h with h h
  · exact h con.2
  · exact h con.1



lemma preChomp_law_prop_transition (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (act : ℕ × ℕ) (hist : List (ℕ × ℕ))
  (leg : Symm_Game_World.law (Chomp height length).toSymm_Game_World (Chomp height length).toSymm_Game_World.init_game_state hist act) :
  Symm_Game_World.transition (Chomp height length).toSymm_Game_World
    (Chomp height length).toSymm_Game_World.init_game_state hist act =
  Symm_Game_World.transition (Chomp height length).toSymm_Game_World
    (Chomp height length).toSymm_Game_World.init_game_state (hist ++ [(length, height)]) act :=
  by
  dsimp [Chomp, preChomp] at *
  by_cases q1 : (0, 0) ∉ hist
  · rw [if_pos ⟨Chomp_init_has_zero height length, q1⟩] at leg
    by_cases q2 : ¬Chomp_state (Chomp_init height length) hist = {(0, 0)}
    · rw [if_pos q2] at *
      have hyp : Chomp_state (Chomp_init height length) (act :: hist) = Chomp_state (Chomp_init height length) (act :: (hist ++ [(length, height)])) :=
        by
        dsimp [Chomp_state]
        apply Finset.filter_congr
        intro x _
        simp_rw [← List.cons_append, List.mem_append]
        constructor
        · intro ca
          rintro q (qdef | qdef)
          · exact ca _ qdef
          · rw [List.mem_singleton] at qdef
            rw [qdef]
            specialize ca act (by apply List.mem_cons_self)
            dsimp [nondomi, domi] at *
            contrapose! ca
            constructor
            · apply le_trans _ ca.1
              have := leg.act_mem
              dsimp [Chomp_init] at this
              rw [Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at this
              exact this.1
            · apply le_trans _ ca.2
              have := leg.act_mem
              dsimp [Chomp_init] at this
              simp_rw [Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at this
              exact this.2
        · intro ca
          intro q qdef
          exact ca _ (Or.inl (qdef))
      by_cases q3 : ¬Chomp_state (Chomp_init height length) (hist ++ [(length, height)]) = {(0, 0)}
      · rw [if_pos q3] at *
        exact hyp
      · rw [if_neg q3]
        rw [not_not] at q3
        rw [hyp]
        dsimp [Chomp_state] at *
        ext x
        constructor
        · intro xdef
          rw [← q3]
          simp_rw [Finset.mem_filter, List.mem_cons] at *
          refine' ⟨xdef.1, _ ⟩
          intro q qdef
          apply xdef.2
          exact Or.inr qdef
        · intro xdef
          rw [Finset.mem_singleton] at xdef
          rw [xdef]
          simp_rw [Finset.mem_filter, List.mem_cons]
          refine' ⟨(Chomp_init_has_zero height length), _ ⟩
          rintro q (qdef | qdef)
          · dsimp [nondomi, domi]
            intro con
            simp_rw [Nat.le_zero] at con
            apply leg.nz_act
            rw [← qdef]
            ext
            · exact con.1
            · exact con.2
          · rw [Finset.ext_iff] at q3
            replace q3 := (q3 (0,0)).mpr (by apply Finset.mem_singleton_self)
            rw [Finset.mem_filter] at q3
            exact q3.2 _ qdef
    · rw [if_neg q2] at *
      rw [not_not] at q2
      split_ifs with H
      · rfl
      · have := Chomp_state_sub (Chomp_init height length) hist [(length, height)]
        have that : Chomp_state (Chomp_init height length) (hist ++ [(length, height)]) ≠ Chomp_state (Chomp_init height length) hist := by rw [q2] ; exact H
        have thus := Finset.ssubset_iff_subset_ne.mpr ⟨this,that⟩
        rw [q2, Finset.ssubset_singleton_iff] at thus
        have thut := Chomp_state_state_empty _ (Chomp_init_has_zero height length) _ thus
        rw [List.mem_append] at thut
        cases' thut with no neither
        · exact False.elim (q1 no)
        · rw [List.mem_singleton, Prod.eq_iff_fst_eq_snd_eq] at neither
          cases' h with h h
          · exact False.elim (h neither.2.symm)
          · exact False.elim (h neither.1.symm)
  · push_neg at q1
    rw [Chomp_state_hist_zero _ hist q1]
    rw [Chomp_state_hist_zero _ (act :: hist) (List.mem_cons_of_mem _ q1)]
    rw [Chomp_state_hist_zero _ (hist ++ [(length, height)]) (List.mem_append_left _ q1)]
    rw [Chomp_state_hist_zero _ (act ::(hist ++ [(length, height)])) (List.mem_cons_of_mem _ (List.mem_append_left _ q1))]


private lemma helper (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) : (0,0) ∉ [(length, height)] :=
  by
  intro con
  rw [List.mem_singleton] at con
  cases' h with h h
  · apply h
    simp_all only [Prod.mk.injEq, ne_eq]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [right, left]
    simp_all only [not_true_eq_false]
  · apply h
    simp_all only [Prod.mk.injEq, ne_eq]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [right, left]
    simp_all only [not_true_eq_false]


lemma Chomp_init_has_len_hei (height length : ℕ) : (length, height) ∈ Chomp_init height length :=
  by
  dsimp [Chomp_init]
  simp_rw [Finset.mem_product, Finset.mem_range]
  constructor
  all_goals {apply Nat.lt_succ_self}

--#exit

lemma preChomp_law_prop_law (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (act : ℕ × ℕ) (hist : List (ℕ × ℕ)) (hh : hist ≠ [])
  (hh2 : (length, height) ∉ hist)
  (leg : Symm_Game_World.law (Chomp height length).toSymm_Game_World (Chomp height length).toSymm_Game_World.init_game_state hist act) :
  Symm_Game_World.law (Chomp height length).toSymm_Game_World (Chomp height length).toSymm_Game_World.init_game_state
  (hist ++ [(length, height)]) act :=
  by
  dsimp [Chomp, preChomp] at *
  by_cases q0 : (0, 0) ∉ hist
  · rw [if_pos ⟨Chomp_init_has_zero height length, q0 ⟩ ] at leg
    rw [if_pos _]
    swap
    · refine' ⟨Chomp_init_has_zero height length, _⟩
      apply List.not_mem_append q0
      intro con
      rw [List.mem_singleton, Prod.eq_iff_fst_eq_snd_eq] at con
      cases' h with h h
      · exact False.elim (h con.2.symm)
      · exact False.elim (h con.1.symm)
    · by_cases q1 : ¬Chomp_state (Chomp_init height length) hist = {(0, 0)}
      · rw [if_pos q1] at leg
        by_cases q2 : ¬Chomp_state (Chomp_init height length) (hist ++ [(length, height)]) = {(0, 0)}
        · rw [if_pos q2]
          constructor
          · exact leg.act_mem
          · intro q qdef
            rw [List.mem_append] at qdef
            cases' qdef with qdef qdef
            · exact leg.hist_mem q qdef
            · rw [List.mem_singleton] at qdef
              rw [qdef]
              apply Chomp_init_has_len_hei
          · rw [List.pairwise_append]
            constructor
            · apply leg.hist_nd
            · constructor
              · apply List.pairwise_singleton
              · intro a ah b bs
                rw [List.mem_singleton] at bs
                rw [bs]
                have ahh := leg.hist_mem a ah
                dsimp [Chomp_init] at ahh
                simp_rw [Finset.mem_product, Finset.mem_range, Nat.lt_succ] at ahh
                intro con
                dsimp [domi] at con
                apply hh2
                convert ah
                · exact le_antisymm con.1 ahh.1
                · exact le_antisymm con.2 ahh.2
          · intro q qdef
            rw [List.mem_append] at qdef
            cases' qdef with qdef qdef
            · exact leg.nd _ qdef
            · rw [List.mem_singleton] at qdef
              rw [qdef]
              dsimp [nondomi, domi]
              cases' hist with x hist
              · contradiction
              · have leg1 := leg.act_mem
                have leg3 := leg.hist_mem x (by exact List.mem_cons_self x hist)
                dsimp [Chomp_init] at leg1 leg3
                simp_rw [Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at leg1 leg3
                have leg2 := leg.nd x (List.mem_cons_self x hist)
                dsimp [nondomi, domi] at leg2
                intro con
                have uno : act.1 = length := le_antisymm leg1.1 con.1
                have dos : act.2 = height := le_antisymm leg1.2 con.2
                rw [← uno, ← dos] at leg3
                exact leg2 leg3
          · exact leg.nz_act
        · rw [if_neg q2]
          exact leg.nz_act
      · rw [if_neg q1] at leg
        rw [not_not] at q1
        rw [if_neg ]
        · exact leg
        · rw [not_not]
          rw [Finset.eq_singleton_iff_unique_mem]
          constructor
          · rw [Chomp_state_has_zero_iff_hist_has_zero]
            · apply List.not_mem_append q0
              exact helper _ _ h
            · apply Chomp_init_has_zero
          · intro x xdef
            replace xdef := Chomp_state_sub _ _ _ xdef
            rw [q1] at xdef
            rw [Finset.mem_singleton] at xdef
            exact xdef
  · rw [not_not] at q0
    rw [if_neg (by rw [not_and_or] ; right ; rw [not_not] ; exact q0)] at leg
    rw [if_neg (by rw [not_and_or] ; right ; rw [not_not] ; exact List.mem_append.mpr (Or.inl q0))]
    trivial




lemma Chomp_History_no_zero (height length : ℕ)  (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  : ∀ t, (0,0) ∉ History_on_turn (Chomp_init height length) f_strat s_strat t :=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    trivial
  · dsimp [History_on_turn]
    split_ifs with q
    · apply List.not_mem_cons_of_ne_of_not_mem _ ih
      specialize f_leg t q
      dsimp [Chomp, preChomp] at f_leg
      rw [if_pos ⟨(Chomp_init_has_zero height length), ih⟩] at f_leg
      split_ifs at f_leg with q2
      · contrapose! f_leg
        exact f_leg.symm
      · intro con
        apply f_leg.nz_act con.symm
    · apply List.not_mem_cons_of_ne_of_not_mem _ ih
      rw [Turn_not_fst_iff_snd] at q
      specialize s_leg t q
      dsimp [Chomp, preChomp] at s_leg
      rw [if_pos ⟨(Chomp_init_has_zero height length), ih⟩] at s_leg
      split_ifs at s_leg with q2
      · contrapose! s_leg
        exact s_leg.symm
      · intro con
        apply s_leg.nz_act con.symm




lemma Chomp_strat_non_zero_fst (height length : ℕ) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat) :
  ∀ t, Turn_fst (t+1) → f_strat (Chomp height length).init_game_state (History_on_turn (Chomp height length).init_game_state f_strat s_strat t) ≠ (0,0) :=
  by
  intro t tf
  have := f_leg t tf
  dsimp [Chomp, preChomp] at this
  rw [if_pos ⟨(Chomp_init_has_zero height length), (Chomp_History_no_zero _ _ _ _ f_leg s_leg  t)⟩] at this
  split_ifs at this with q2
  · exact this
  · intro con
    apply this.nz_act con


lemma Chomp_strat_non_zero_snd (height length : ℕ) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat) :
  ∀ t, Turn_snd (t+1) → s_strat (Chomp height length).init_game_state (History_on_turn (Chomp height length).init_game_state f_strat s_strat t) ≠ (0,0) :=
  by
  intro t tf
  have := s_leg t tf
  dsimp [Chomp, preChomp] at this
  rw [if_pos ⟨(Chomp_init_has_zero height length), (Chomp_History_no_zero _ _ _ _ f_leg s_leg  t)⟩] at this
  split_ifs at this with q2
  · exact this
  · intro con
    apply this.nz_act con




lemma Chomp_state_on_turn_has_zero (height length : ℕ)  (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  :
  ∀ t, (0,0) ∈ (Chomp height length).state_on_turn f_strat s_strat t :=
  by
  intro t
  cases' t with t
  · dsimp [Symm_Game_World.state_on_turn]
    dsimp [Chomp, preChomp, Symm_Game_World.history_on_turn, History_on_turn]
    apply Chomp_init_has_zero
  · dsimp [Symm_Game_World.state_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q]
      dsimp [Chomp, preChomp]
      by_cases q1 : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat t) = {(0,0)}
      · rw [if_neg (by rw [not_not] ; apply q1)]
        exact Finset.mem_singleton.mpr rfl
      · rw [if_pos (by apply q1)]
        rw [Chomp_state_has_zero_iff_hist_has_zero _ (by apply Chomp_init_has_zero)]
        apply List.not_mem_cons_of_ne_of_not_mem
        · exact (Chomp_strat_non_zero_fst _ _ _ _ f_leg s_leg t q).symm
        · apply (Chomp_History_no_zero _ _ _ _ f_leg s_leg  t)
    · rw [if_neg q]
      rw [Turn_not_fst_iff_snd] at q
      dsimp [Chomp, preChomp]
      by_cases q1 : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat t) = {(0,0)}
      · rw [if_neg (by rw [not_not] ; apply q1)]
        exact Finset.mem_singleton.mpr rfl
      · rw [if_pos (by apply q1)]
        rw [Chomp_state_has_zero_iff_hist_has_zero _ (by apply Chomp_init_has_zero)]
        apply List.not_mem_cons_of_ne_of_not_mem
        · exact (Chomp_strat_non_zero_snd _ _ _ _ f_leg s_leg t q).symm
        · apply (Chomp_History_no_zero _ _ _ _ f_leg s_leg  t)





lemma Chomp_state_on_turn_sub (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  :
  ∀ t, ((Chomp height length).state_on_turn f_strat s_strat (t+1)) ⊆ (Chomp height length).state_on_turn f_strat s_strat t :=
  by
  intro t
  cases' t with t
  · dsimp [Symm_Game_World.state_on_turn]
    rw [if_pos (by decide)]
    dsimp [Chomp, preChomp, Symm_Game_World.history_on_turn, History_on_turn]
    rw [if_pos (by apply Chomp_state_ini_not_zero _ _ h)]
    apply Chomp_state_sub_ini
  · dsimp [Symm_Game_World.state_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q]
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      dsimp [Chomp, preChomp]
      rw [← Turn_fst_not_step] at q
      by_cases q1 : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat t) = {(0,0)}
      · have : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat (t+1)) = {(0,0)} :=
          by
          dsimp [Symm_Game_World.history_on_turn, History_on_turn]
          rw [if_pos q]
          apply Chomp_state_zero_act_non_zero
          · apply Chomp_init_has_zero
          · exact q1
          · apply Chomp_strat_non_zero_fst _ _ _ _ f_leg s_leg t q
        rw [if_neg (by rw [not_not] ; apply this), if_neg (by rw [not_not] ; apply q1)]
      · by_cases q2 : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat (t+1)) = {(0,0)}
        · rw [if_neg (by rw [not_not]; apply q2)]
          rw [if_pos (by apply q1)]
          rw [Finset.singleton_subset_iff]
          rw [Chomp_state_has_zero_iff_hist_has_zero _ (by apply Chomp_init_has_zero)]
          apply List.not_mem_cons_of_ne_of_not_mem
          · exact (Chomp_strat_non_zero_fst _ _ _ _ f_leg s_leg t q).symm
          · apply (Chomp_History_no_zero _ _ _ _ f_leg s_leg  t)
        · rw [if_pos (by apply q2)]
          rw [if_pos (by apply q1)]
          apply Chomp_state_sub_of_hist_sub
          dsimp [Symm_Game_World.history_on_turn, History_on_turn]
          rw [if_pos q]
          exact fun ⦃a⦄ a_1 =>
            List.Mem.tail
              (s_strat (Chomp_init height length)
                (f_strat (Chomp_init height length)
                    (History_on_turn (Chomp_init height length) f_strat s_strat t) ::
                  History_on_turn (Chomp_init height length) f_strat s_strat t))
              a_1
    · rw [if_neg q]
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q]
      dsimp [Chomp, preChomp]
      replace q := not_not.mpr q -- rw fails, pathetic
      rw [← Turn_fst_not_step] at q
      by_cases q1 : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat t) = {(0,0)}
      · have : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat (t+1)) = {(0,0)} :=
          by
          dsimp [Symm_Game_World.history_on_turn, History_on_turn]
          rw [if_neg q]
          apply Chomp_state_zero_act_non_zero
          · apply Chomp_init_has_zero
          · exact q1
          · apply Chomp_strat_non_zero_snd _ _ _ _ f_leg s_leg t q
        rw [if_neg (by rw [not_not] ; apply this), if_neg (by rw [not_not] ; apply q1)]
      · by_cases q2 : Chomp_state (Chomp_init height length) ((Chomp height length).history_on_turn f_strat s_strat (t+1)) = {(0,0)}
        · rw [if_neg (by rw [not_not]; apply q2)]
          rw [if_pos (by apply q1)]
          rw [Finset.singleton_subset_iff]
          rw [Chomp_state_has_zero_iff_hist_has_zero _ (by apply Chomp_init_has_zero)]
          apply List.not_mem_cons_of_ne_of_not_mem
          · exact (Chomp_strat_non_zero_snd _ _ _ _ f_leg s_leg t q).symm
          · apply (Chomp_History_no_zero _ _ _ _ f_leg s_leg  t)
        · rw [if_pos (by apply q2)]
          rw [if_pos (by apply q1)]
          apply Chomp_state_sub_of_hist_sub
          dsimp [Symm_Game_World.history_on_turn, History_on_turn]
          rw [if_neg q]
          exact fun ⦃a⦄ a_1 =>
            List.Mem.tail
              (f_strat (Chomp_init height length)
                (s_strat (Chomp_init height length)
                    (History_on_turn (Chomp_init height length) f_strat s_strat t) ::
                  History_on_turn (Chomp_init height length) f_strat s_strat t))
              a_1


lemma Chomp_state_empty  (ini : (Finset (ℕ × ℕ))) : Chomp_state ini [] = ini :=
  by
  dsimp [Chomp_state]
  rw [Finset.filter_eq_self]
  intro _ _ _ no
  contradiction

lemma Chomp_not_mem_state_of_mem_hist (ini : (Finset (ℕ × ℕ))) (hist : (List (ℕ × ℕ))) (act : ℕ × ℕ) (ha : act ∈ hist) : act ∉ Chomp_state ini hist :=
  by
  dsimp [Chomp_state]
  intro con
  rw [Finset.mem_filter] at con
  replace con := con.2 _ ha
  apply con
  dsimp [domi]
  exact ⟨le_refl act.1, le_refl act.2⟩


lemma Chomp_state_eq_state_on_turn (height length : ℕ) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (t : ℕ) :
  (Chomp height length).state_on_turn f_strat s_strat t = Chomp_state (Chomp height length).init_game_state (History_on_turn (Chomp height length).init_game_state f_strat s_strat t) :=
  by
  cases' t with t
  · dsimp [Symm_Game_World.state_on_turn, History_on_turn]
    rw [Chomp_state_empty]
  · dsimp [Symm_Game_World.state_on_turn, History_on_turn]
    by_cases q : Turn_fst (t + 1)
    · simp_rw [if_pos q]
      dsimp [Chomp, preChomp]
      split_ifs with q2
      · dsimp [Symm_Game_World.history_on_turn] at q2
        rw [eq_comm]
        apply Chomp_state_zero_act_non_zero
        · apply Chomp_init_has_zero
        · exact q2
        · apply Chomp_strat_non_zero_fst _ _ _ _ f_leg s_leg t q
      · rfl
    · simp_rw [if_neg q]
      dsimp [Chomp, preChomp]
      split_ifs with q2
      · dsimp [Symm_Game_World.history_on_turn] at q2
        rw [eq_comm]
        apply Chomp_state_zero_act_non_zero
        · apply Chomp_init_has_zero
        · exact q2
        · apply Chomp_strat_non_zero_snd _ _ _ _ f_leg s_leg t q
      · rfl

lemma Chomp_act_mem_state_of_law (ini : (Finset (ℕ × ℕ))) (hist : (List (ℕ × ℕ))) (act : ℕ × ℕ) (leg : Chomp_law ini hist act) :
  act ∈ Chomp_state ini hist :=
  by
  dsimp [Chomp_state]
  rw [Finset.mem_filter]
  exact ⟨leg.act_mem, leg.nd ⟩




lemma Chomp_state_cons_eq (ini : (Finset (ℕ × ℕ))) (hist : (List (ℕ × ℕ))) (act : ℕ × ℕ)
  (main : Chomp_state ini (act :: hist) = Chomp_state ini hist) :
  ¬ Chomp_law ini hist act :=
  by
  intro con
  replace con := Chomp_act_mem_state_of_law _ _ _ con
  rw [← main] at con
  dsimp [Chomp_state] at con
  rw [Finset.mem_filter] at con
  replace con := con.2 act (by exact List.mem_cons_self act hist)
  apply con
  exact ⟨le_refl act.1, le_refl act.2⟩



--#exit

lemma Chomp_state_on_turn_sub_strict (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (t : ℕ) (hs : (Chomp height length).state_on_turn f_strat s_strat t ≠ {(0,0)}):
  ((Chomp height length).state_on_turn f_strat s_strat (t+1)) ⊂ (Chomp height length).state_on_turn f_strat s_strat t :=
  by
  rw [Finset.ssubset_iff_subset_ne]
  refine' ⟨Chomp_state_on_turn_sub _ _ h _ _ f_leg s_leg t, _ ⟩
  intro con
  simp_rw [Chomp_state_eq_state_on_turn _ _ _ _ f_leg s_leg] at *
  dsimp [History_on_turn] at con
  by_cases q : Turn_fst (t + 1)
  · rw [if_pos q] at con
    have := f_leg t q
    dsimp [Chomp, preChomp] at this
    rw [if_pos ⟨Chomp_init_has_zero _ _ , Chomp_History_no_zero _ _ _ _ f_leg s_leg  t⟩] at this
    rw [if_pos (by apply hs)] at this
    replace con := Chomp_state_cons_eq _ _ _ con
    exact con this
  · rw [if_neg q] at con
    have := s_leg t q
    dsimp [Chomp, preChomp] at this
    rw [if_pos ⟨Chomp_init_has_zero _ _ , Chomp_History_no_zero _ _ _ _ f_leg s_leg  t⟩] at this
    rw [if_pos (by apply hs)] at this
    replace con := Chomp_state_cons_eq _ _ _ con
    exact con this

lemma Chomp_state_zero_stays (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (t : ℕ) (hs : (Chomp height length).state_on_turn f_strat s_strat t = {(0,0)}) :
  (Chomp height length).state_on_turn f_strat s_strat (t + 1) = {(0,0)} :=
  by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine' ⟨Chomp_state_on_turn_has_zero _ _ _ _ f_leg s_leg (t+1), _ ⟩
  intro x xdef
  replace xdef := (Chomp_state_on_turn_sub _ _ h _ _ f_leg s_leg t) xdef
  rw [hs, Finset.mem_singleton] at xdef
  exact xdef

-- lemma Chomp_state_reaches_zero (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
--   (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
--   (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat) :
--   ∃ t, (Chomp height length).state_on_turn f_strat s_strat t = {(0,0)} :=
--   by
--   by_contra! con
--   have ohoh := fun t => Finset.card_lt_card ((Chomp_state_on_turn_sub_strict _ _ h _ _ f_leg s_leg t) (con t))
--   have nonono : ∀ t, (Symm_Game_World.state_on_turn (Chomp height length).toSymm_Game_World f_strat s_strat t).card < ((length +1) * (height + 1)) - t :=


-- #check Finset.card_eq_one
-- #check Finset.card_lt_card


lemma Chomp_state_zero_stays_strong (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (f_strat s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (s_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law f_strat s_strat)
  (t : ℕ) (hs : (Chomp height length).state_on_turn f_strat s_strat t = {(0,0)}) :
  ∀ n, (Chomp height length).state_on_turn f_strat s_strat (t + n) = {(0,0)} :=
  by
  intro n
  induction' n with n ih
  · exact hs
  · rw [Nat.add_succ]
    apply Chomp_state_zero_stays  _ _ h _ _ f_leg s_leg (t+n) ih


lemma Chomp_WLT (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) : (Chomp height length).isWL_wBound ((length +1) * (height + 1)) :=
  by
  intro f_strat s_strat f_leg s_leg
  use ((length +1) * (height + 1))
  refine' ⟨le_refl ((length +1) * (height + 1)), _ ⟩
  dsimp [Symm_Game_World.Turn_isWL, Chomp, preChomp]
  by_contra! con
  have dec : ∀ t ≤ ((length +1) * (height + 1)), (Symm_Game_World.state_on_turn (Chomp height length).toSymm_Game_World f_strat s_strat t).card ≤ ((length +1) * (height + 1)) - t :=
    by
    intro t tdef
    have : ∀ t ≤ ((length +1) * (height + 1)), (Symm_Game_World.state_on_turn (Chomp height length).toSymm_Game_World f_strat s_strat t) ≠  {(0,0)} :=
      by
      intro n ndef con'
      have := Chomp_state_zero_stays_strong _ _ h _ _ f_leg s_leg n con' (((length +1) * (height + 1)) - n)
      rw [Nat.add_sub_cancel' ndef] at this
      exact con this
    induction' t with t ih
    · dsimp [Symm_Game_World.state_on_turn, Chomp, preChomp, Chomp_init]
      simp_rw [Finset.card_product, Finset.card_range]
      apply le_refl
    · have that := Finset.card_lt_card ((Chomp_state_on_turn_sub_strict _ _ h _ _ f_leg s_leg t) (this t (by apply le_trans _ tdef ; apply Nat.le_succ )))
      rw [Nat.lt_iff_add_one_le] at that
      rw [Nat.sub_succ', Nat.le_sub_iff_add_le (by rw [Nat.le_sub_iff_add_le, add_comm] ; apply tdef ; apply le_trans _ tdef ; apply Nat.le_succ)]
      exact le_trans that (ih (by apply le_trans _ tdef ; apply Nat.le_succ ))
  specialize dec ((length +1) * (height + 1)) (le_refl _)
  rw [Nat.sub_self, Nat.le_zero, Finset.card_eq_zero] at dec
  apply Finset.not_mem_empty (0,0)
  rw [← dec]
  apply Chomp_state_on_turn_has_zero _ _ _ _ f_leg s_leg
