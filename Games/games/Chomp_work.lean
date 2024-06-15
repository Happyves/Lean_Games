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
  nd : ∀ q ∈ hist, nondomi q act
  nz_act : act ≠ (0,0)

--@[mk_iff]
structure partiality_condition (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) : Prop where
  zero_ini : (0,0) ∈ ini
  zero_hist : (0,0) ∉ hist
  hist_ini : ∀ a ∈ hist, a ∈ ini
  state : Chomp_state ini hist ≠ {(0,0)}


-- instance (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) : Decidable (partiality_condition ini hist) :=
--   by
--   apply decidable_of_iff'

-- #exit

instance (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) : Decidable (partiality_condition ini hist) :=
  by
  have one : Decidable ((0,0) ∈ ini) := by exact Finset.decidableMem (0, 0) ini
  have two : Decidable ((0,0) ∉ hist) := by exact Not.decidable
  have three : Decidable (∀ a ∈ hist, a ∈ ini) := by exact List.decidableBAll (fun x => x ∈ ini) hist
  have four : Decidable (Chomp_state ini hist ≠ {(0,0)}) := by exact Not.decidable
  cases' one with one one
  · apply Decidable.isFalse
    intro con
    exact one con.zero_ini
  · cases' two with two two
    · apply Decidable.isFalse
      intro con
      exact two con.zero_hist
    · cases' three with three three
      · apply Decidable.isFalse
        intro con
        exact three con.hist_ini
      · cases' four with four four
        · apply Decidable.isFalse
          intro con
          exact four con.state
        · apply Decidable.isTrue
          exact ⟨one, two,three, four⟩



def preChomp (height length : ℕ) : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := Chomp_init height length
  win_states := (fun state => state = {(0,0)})
  transition := fun ini hist act => if Chomp_state ini hist ≠ {(0,0)}
                                    then (Chomp_state ini) (act :: hist)
                                    else {(0,0)}
  law := fun ini hist act => if partiality_condition ini hist
                             then
                              if Chomp_state ini hist ≠ {(0,0)}
                              then Chomp_law ini hist act
                              else act ≠ (0,0) -- saves ass in `preChomp_law_careless`
                             else True



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

--#exit

lemma Chomp_hist_ini_of_Hist_legal (height length : ℕ) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (prehist : List (ℕ × ℕ))
  (main : Hist_legal (preChomp height length).law (preChomp height length).law ini prehist) : ∀ a ∈ prehist, a ∈ ini :=
  by
  induction' prehist with x l ih
  · intro a no ; contradiction
  · cases' main
    rename_i sofar now
    · split_ifs at now
      all_goals { dsimp [preChomp] at now
                  rw [if_pos (⟨ hini, , ⟩ : partiality_condition ini l) ] at now
                }


--#exit

lemma Chomp_hist_no_zero_of_Hist_legal (height length : ℕ) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (prehist : List (ℕ × ℕ))
  (main : Hist_legal (preChomp height length).law (preChomp height length).law ini prehist) : (0,0) ∉ prehist ∧ (∀ a ∈ prehist, a ∈ ini) :=
  by
  induction' prehist with x l ih
  · constructor
    · decide
    · intro a no ; contradiction
  · cases' main
    rename_i sofar now
    constructor
    · apply List.not_mem_cons_of_ne_of_not_mem
      · split_ifs at now
        all_goals { dsimp [preChomp] at now
                    rw [if_pos ⟨hini, (ih sofar).1, (ih sofar).2⟩ ] at now
                    split_ifs at now
                    · contrapose! now
                      apply now.symm
                    · rw [ne_comm]
                      apply now.nz_act}
      · exact (ih sofar).1
    · intro a adef
      rw [List.mem_cons] at adef
      cases' adef with adef adef
      · rw [adef]
        split_ifs at now
        all_goals { dsimp [preChomp] at now
                    rw [if_pos ⟨hini, (ih sofar).1, (ih sofar).2⟩ ] at now
                    split_ifs at now
        }

#exit

lemma preChomp_law_careless (height length : ℕ) :
  careless (preChomp height length).law (preChomp height length).law (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).transition :=
  by
  intro ini hist prehist pHne pHl
  ext act
  by_cases fix : partiality_condition ini hist
  · constructor
    · intro c
      dsimp [preChomp] at c
      rw [if_pos ⟨fix.zero_ini, (by apply List.not_mem_append fix.zero_hist ; exact Chomp_hist_no_zero_of_Hist_legal height length ini fix.zero_ini prehist pHl) , _⟩ ] at c
      by_cases q1 : Chomp_state ini (hist ++ prehist) ≠ {(0,0)}
      · rw [if_pos q1] at c
        by_cases q2 : Chomp_state (Symm_Game_World.transition (preChomp height length) ini (List.tail prehist) (List.head prehist pHne)) (hist) ≠ {(0,0)}
        · dsimp [preChomp] at *
          rw [if_pos q2]
          rw [List.cons_head_tail] at *
          by_cases q3 : Chomp_state ini (List.tail prehist) ≠ {(0, 0)}
          · rw [if_pos q3] at *
            split_ifs
            all_goals { constructor
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
            rw [if_pos] at c
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
            · rw [Chomp_state_has_zero_iff_hist_has_zero ini fix.1 prehist]
              exact ⟨Chomp_hist_no_zero_of_Hist_legal height length ini fix.1 prehist pHl, fix.2⟩
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

#exit


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
  intro ini hist
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
      · dsimp [Chomp_state] at act_mem
        rw [Finset.mem_filter] at act_mem
        exact act_mem.2
      · exact act_nz
    · use (0,0)
  · simp_rw [if_neg q]
    use (1,0)
    split_ifs
    · decide


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



lemma preChomp_law_prop_law (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (act : ℕ × ℕ) (hist : List (ℕ × ℕ)) (hh : hist ≠ [])
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
            · exact leg.nd _ qdef
            · rw [List.mem_singleton] at qdef
              rw [qdef]
              dsimp [nondomi, domi]
              induction' hist with x hist ih
              · contradiction
              · have leg1 := leg.act_mem
                dsimp [Chomp_init] at leg1
                simp_rw [Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at leg1
                have leg2 := leg.nd x (List.mem_cons_self x hist)

          · exact leg.nz_act
        · rw [if_neg q2]
          exact leg.nz_act
      · rw [if_neg q1] at leg



#exit

lemma preChomp_law_prop (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) : Strong_stealing_condition (Chomp height length ) :=
  by
  use (length, height)
  constructor
  · dsimp [Chomp, preChomp]
    rw [if_pos ⟨Chomp_init_has_zero height length , (by apply List.not_mem_nil)⟩]
    rw [if_pos (Chomp_state_ini_not_zero _ _ h)]
    dsimp [Chomp_init]
    constructor
    · simp only [Finset.mem_product, Finset.mem_range, lt_add_iff_pos_right, zero_lt_one, and_self]
    · intro q no ; contradiction
    · simp_all only [ne_eq, Prod.mk.injEq, not_and]
      intro a
      aesop_subst a
      simp_all only [not_true_eq_false, or_false, not_false_eq_true]
  · intro act hist leg hh
    constructor
    · exact preChomp_law_prop_transition height length h act hist leg
    · sorry
