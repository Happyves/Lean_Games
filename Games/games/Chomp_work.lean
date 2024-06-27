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

lemma Chomp_state_cons (ini : Finset (ℕ × ℕ)) (l :  List (ℕ × ℕ)) (x : ℕ × ℕ) :
  Chomp_state ini (x :: l) ⊆ Chomp_state ini l :=
  by
  rw [List.cons_eq_singleton_append]
  apply Chomp_state_sub'


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


inductive Chomp_law (ini : Finset (ℕ × ℕ)) : List (ℕ × ℕ) → ℕ × ℕ →  Prop where
| nil (act : ℕ × ℕ) : (if ini ≠ {(0,0)} then  act ∈ ini ∧ act ≠ (0,0) else act ≠ (0,0))→ Chomp_law ini [] act
| cons (act : ℕ × ℕ) (l : List (ℕ × ℕ)) (x : ℕ × ℕ) : Chomp_law ini l x →
          (if Chomp_state ini (x :: l) ≠ {(0,0)} then act ∈ Chomp_state ini (x :: l) else True) →
          act ≠ (0,0) → Chomp_law ini (x :: l) act


-- instance (ini :  Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ))  : DecidablePred (Chomp_law ini hist) :=
--   by
--   induction' hist with x l ih
--   · intro act
--     have : Decidable (act ∈ ini ∧ act ≠ (0,0)) := by exact And.decidable
--     cases' this with h h
--     · apply isFalse
--       intro con
--       cases' con with _ no nope
--       exact h ⟨no,nope⟩
--     · apply isTrue
--       exact Chomp_law.nil act h.1 h.2
--   · intro act
--     specialize ih x
--     have : Decidable (Chomp_law ini l x ∧ act ∈ Chomp_state ini (x :: l) ∧ act ≠ (0,0)) :=
--       by exact And.decidable
--     cases' this with h h
--     · apply isFalse
--       intro con
--       cases' con with _  _ _ _  _ _ no nope nada -- cases kind of broken ???
--       exact h ⟨no,nope, nada⟩
--     · apply isTrue
--       exact Chomp_law.cons act _ _ h.1 h.2.1 h.2.2



def preChomp (height length : ℕ) : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := Chomp_init height length
  win_states := (fun state => state = {(0,0)})
  transition := fun ini hist act => if Chomp_state ini hist ≠ {(0,0)}
                                    then (Chomp_state ini) (act :: hist)
                                    else {(0,0)}
  law := fun ini hist act => if (0,0) ∈ ini ∧ (0,0) ∉ hist
                             then Chomp_law ini hist act
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



lemma Chomp_law_ini_zero (hist : List (ℕ × ℕ)) (hh : (0,0) ∉ hist) : ∀ act : (ℕ × ℕ), act ≠ (0,0) → Chomp_law {(0,0)} hist act :=
  by
  induction' hist with x l ih
  · intro a anz
    apply Chomp_law.nil
    rw [if_neg (by decide)]
    exact anz
  · intro a anz
    apply Chomp_law.cons
    · apply ih
      · simp_all only [ne_eq, Prod.forall, Prod.mk.injEq, not_and, List.mem_cons]
        unhygienic with_reducible aesop_destruct_products
        simp_all only [Prod.mk.injEq, not_and]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [not_true_eq_false, IsEmpty.forall_iff, or_true]
      · simp_all only [ne_eq, Prod.forall, Prod.mk.injEq, not_and, List.mem_cons]
        unhygienic with_reducible aesop_destruct_products
        simp_all only [Prod.mk.injEq, not_and]
        intro a
        aesop_subst a
        simp_all only [true_and]
        apply Aesop.BuiltinRules.not_intro
        intro a
        aesop_subst a
        simp_all only [true_or, not_true_eq_false]
    · split_ifs
      rename_i problem
      exfalso
      apply problem
      apply Chomp_state_ini_zero _ hh
    · exact anz



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

lemma Chomp_state_mem_state_not_hist_zero (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) (main : act ∈ Chomp_state ini hist) :
  (0,0) ∉ hist :=
  by
  have := Finset.ne_empty_of_mem main
  have that := (Chomp_state_hist_zero ini hist)
  rw [← not_imp_not] at that
  exact that this


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

lemma Chomp_state_empty_hist (ini : Finset ( ℕ × ℕ)) : Chomp_state ini [] = ini :=
  by
  dsimp [Chomp_state]
  rw [Finset.filter_eq_self]
  intro _ _ _ no
  contradiction

lemma Chomp_law_state_mem (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) (leg : Chomp_law ini hist act)
  (no_end : Chomp_state ini hist ≠ {(0,0)}):
  act ∈ Chomp_state ini hist :=
  by
  dsimp [Chomp_state]
  rw [Finset.mem_filter]
  cases' hist with x l
  · cases' leg
    rename_i a
    rw [Chomp_state_empty_hist] at no_end
    rw [if_pos no_end] at a
    exact ⟨a.1, fun q qdef => (by contradiction) ⟩
  · cases' leg
    rename_i a b c
    rw [if_pos no_end] at c
    dsimp [Chomp_state] at c
    rw [Finset.mem_filter] at c
    exact c




lemma Chomp_law_ini_mem (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) (leg : Chomp_law ini hist act)
  (no_end : Chomp_state ini hist ≠ {(0,0)}) :
  act ∈ ini  :=
  by
  apply Chomp_state_sub_ini _ hist
  apply Chomp_law_state_mem _ _ _ leg no_end



lemma Chomp_law_act_nz (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) (leg : Chomp_law ini hist act) :
  act ≠ (0, 0) :=
  by
  cases' hist with x l
  · cases' leg
    rename_i a
    split_ifs at a
    · exact a.2
    · exact a
  · cases' leg
    rename_i _ a _
    exact a




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
                  apply (Chomp_law_act_nz _ _ _ now).symm}
    · exact ih sofar

--#exit



lemma Chomp_hist_legal (height length : ℕ) (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (prehist hist : List (ℕ × ℕ)) (act : ℕ × ℕ)
  (Hleg : Hist_legal (preChomp height length).law (preChomp height length).law ini prehist)
  : Chomp_law ini (hist ++ prehist) act ↔  Chomp_law (Chomp_state ini prehist) (hist) act :=
  by
  revert act
  induction' hist with x l ih
  · intro act
    constructor
    · intro main
      cases' main
      · rename_i h
        rw [Chomp_state_empty_hist]
        apply Chomp_law.nil
        exact h
      · rename_i l x h1 h2 h3
        apply Chomp_law.nil
        split_ifs with h
        · rw [if_pos h] at h2
          exact ⟨ h2,h3⟩
        · exact h3
    · intro main
      cases' main
      rename_i h
      revert act
      cases' prehist with x l
      · intro act h
        apply Chomp_law.nil
        rwa [Chomp_state_empty_hist] at h
      · intro act h
        have lnz : (0, 0) ∉ l :=
          by
          intro con
          have : Chomp_state ini (x :: l) ≠ {(0, 0)} :=
            by
            rw [Chomp_state_hist_zero _ _ (by exact List.Mem.tail x con)]
            intro con'
            apply Finset.singleton_ne_empty _ con'.symm
          rw [if_pos this] at h
          rw [Chomp_state_hist_zero _ _ (by exact List.Mem.tail x con)] at h
          exact Finset.not_mem_empty _ h.1
        dsimp
        apply Chomp_law.cons
        · cases' Hleg
          rename_i sofar now
          dsimp [preChomp] at now
          split_ifs at now
          · exact now
          · rename_i no ; exact False.elim (no ⟨ hini, lnz⟩)
          · exact now
          · rename_i no ; exact False.elim (no ⟨ hini, lnz⟩)
        · split_ifs with q
          rw [if_pos q] at h
          exact h.1
        · split_ifs at h
          · exact h.2
          · exact h
  · intro act
    constructor
    · intro main
      rw [List.cons_append] at main
      cases' main
      rename_i h1 h2 h3
      apply Chomp_law.cons _ _ _ _ _ h2
      · rw [← ih]
        exact h1
      · rw [Chomp_state_blind, List.cons_append]
        exact h3
    · intro main
      rw [List.cons_append]
      cases' main
      rename_i h1 h2 h3
      apply Chomp_law.cons _ _ _ _ _ h2
      · rw [ih]
        exact h1
      · rw [Chomp_state_blind] at h3
        exact h3

#check Hist_legal.rec

--#exit


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
      induction' hist with x l ih
      · dsimp [preChomp]
        split_ifs
        · apply Chomp_law.nil
          rw [if_neg (by decide)]
          apply Chomp_law_act_nz _ _ _ c
        · rw [List.cons_head_tail, ← Chomp_hist_legal _ _ _ fix.1 _ _ _ pHl]
          exact c
      · dsimp [preChomp]
        split_ifs
        · apply Chomp_law.cons
          · apply Chomp_law_ini_zero
            · intro con
              rename_i no
              apply no.2
              exact List.mem_cons_of_mem x con
            · intro con
              rename_i no
              apply no.2
              rw [con]
              exact List.mem_cons_self (0, 0) l
          · split_ifs
            rename_i no problem
            exfalso
            apply problem
            apply Chomp_state_ini_zero _ no.2
          · apply Chomp_law_act_nz _ _ _ c
        · rw [List.cons_head_tail, List.cons_eq_singleton_append, ← Chomp_hist_legal _ _ _ fix.1 _ _ _ pHl]
          rw [← List.cons_eq_singleton_append]
          exact c
    · intro c
      dsimp [preChomp] at *
      rw [if_pos ⟨fix.1, (by apply List.not_mem_append fix.2 ; exact Chomp_hist_no_zero_of_Hist_legal height length ini fix.1 prehist pHl)⟩ ]
      split_ifs at c
      · revert act
        induction' hist with x l ih
        · intro act c
          rename_i h1 h2
          -- use h1 to show that state at prehist and pHl is 0, so that only requirements are legality and act non-zero, which we get from c
          sorry
        · intro act c
          rename_i h1 h2
          rw [List.cons_append]
          apply Chomp_law.cons
          · apply ih ⟨fix.1, List.not_mem_of_not_mem_cons fix.2⟩ ⟨h2.1, List.not_mem_of_not_mem_cons fix.2⟩
            apply Chomp_law_ini_zero _ (List.not_mem_of_not_mem_cons fix.2)
            intro con
            apply fix.2
            rw [con]
            exact List.mem_cons_self (0, 0) l
          · rw [if_neg]
            · trivial
            · rw [not_not, ← List.cons_append]
              have : Chomp_state ini (x :: l ++ prehist) ⊆ Chomp_state ini (prehist.tail) :=
                by
                nth_rewrite 1 [← List.cons_head_tail _ pHne]
                rw [List.append_cons]
                apply Chomp_state_sub'
              rw [h1] at this
              rw [Finset.eq_singleton_iff_unique_mem]
              constructor
              · rw [Chomp_state_has_zero_iff_hist_has_zero _ fix.1]
                apply List.not_mem_append fix.2
                apply Chomp_hist_no_zero_of_Hist_legal height length _ fix.1 _  pHl
              · intro y ydef
                specialize this ydef
                rw [Finset.mem_singleton] at this
                exact this
          · apply Chomp_law_act_nz _ _ _ c
      · rename_i no
        exfalso
        apply no
        exact ⟨ (by exact Finset.mem_singleton.mpr rfl), fix.2 ⟩
      · sorry
      · rename_i no
        exfalso
        apply no
        rw [List.cons_head_tail]
        refine' ⟨_, fix.2⟩
        rw [Chomp_state_has_zero_iff_hist_has_zero _ fix.1]
        exact Chomp_hist_no_zero_of_Hist_legal height length _ fix.1 _ pHl
  · dsimp [preChomp]
    rw [if_neg (by push_neg at * ;intro _ ; simp_all only [ne_eq, forall_true_left, List.mem_append, true_or] )]
    simp only [ite_not, true_iff]
    split_ifs
    · exfalso
      apply fix
      rename_i h2 h1
      refine' ⟨_ , h1.2⟩
      apply Chomp_state_sub_ini  ini (List.tail prehist)
      rw [h2]
      exact Finset.mem_singleton.mpr rfl
    · exfalso
      apply fix
      rename_i _ h1
      refine' ⟨_ , h1.2⟩
      apply Chomp_state_sub_ini ini (List.head prehist pHne :: List.tail prehist)
      exact h1.1


#check List.not_mem_of_not_mem_cons


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
              exact (Chomp_law_act_nz _ _ _ f_leg)
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
              exact (Chomp_law_act_nz _ _ _ s_leg)
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
              exact (Chomp_law_act_nz _ _ _ f_leg)
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
              exact (Chomp_law_act_nz _ _ _ s_leg)
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
  split_ifs
  · use (1,0)
    decide
  · rename_i h1 h2
    induction' hist with x l ih
    · rw [Chomp_state_empty_hist] at h2
      have : ∃ x ∈ ini, x ≠ (0,0) :=
        by
        by_contra! con
        apply h2
        ext y
        constructor
        · intro h
          rw [Finset.mem_singleton]
          exact con y h
        · rw [Finset.mem_singleton]
          intro h
          rw [h]
          exact h1.1
      obtain ⟨ x, xini, xnz ⟩ := this
      use x
      apply Chomp_law.nil x xini xnz
    ·
  · use (0,0)
  -- by_cases q : ¬Chomp_state ini hist = {(0, 0)}
  -- · simp_rw [if_pos q]
  --   split_ifs
  --   · have : ∃ act, act ∈ Chomp_state ini hist ∧ act ≠ (0,0) :=
  --       by
  --       contrapose! q
  --       ext x
  --       constructor
  --       · intro xdef
  --         specialize q x xdef
  --         rename_i h
  --         aesop_subst q
  --         simp_all only [gt_iff_lt, Finset.mem_singleton]
  --       · intro xdef
  --         rw [Finset.mem_singleton] at xdef
  --         rw [xdef]
  --         dsimp [Chomp_state]
  --         rw [Finset.mem_filter]
  --         rename_i gain
  --         refine' ⟨gain.1, _ ⟩
  --         intro q qdef
  --         dsimp [nondomi, domi]
  --         intro con
  --         simp_rw [Nat.le_zero] at con
  --         apply gain.2
  --         convert qdef
  --         · exact con.1.symm
  --         · exact con.2.symm
  --     obtain ⟨act, act_mem, act_nz⟩ := this
  --     use act
  --     --revert act
  --     induction' hist with x l ih
  --     · --intro act act_mem act_nz
  --       apply Chomp_law.nil _ _ act_nz
  --       rw [Chomp_state_empty_hist] at act_mem
  --       exact act_mem
  --     · --intro act act_mem act_nz
  --       apply Chomp_law.cons _ _ _ _ act_mem act_nz
  --       rename_i h
  --       apply ih
  --       · contrapose! q
  --         apply Chomp_state_zero_act_non_zero _ h.1 _ _ q
  --         intro con
  --         rw [con] at h
  --         apply h.2
  --         exact List.mem_cons_self (0, 0) l
  --       · refine' ⟨ h.1, _ ⟩
  --         intro con
  --         apply h.2
  --         exact List.mem_cons_of_mem x con
  --       · apply Chomp_state_cons _ _ _ act_mem
  --   · use (0,0)
  -- · simp_rw [if_neg q]
  --   use (1,0)
  --   split_ifs
  --   · decide

#check Chomp_law.rec

#exit

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
              have := (Chomp_law_state_mem _ _ _ leg)
              dsimp [Chomp_state, Chomp_init] at this
              simp_rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at this
              exact this.1.1
            · apply le_trans _ ca.2
              have := (Chomp_law_state_mem _ _ _ leg)
              dsimp [Chomp_state, Chomp_init] at this
              simp_rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at this
              exact this.1.2
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
            apply (Chomp_law_act_nz _ _ _ leg)
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
          induction' hist with x l ih
          · contradiction
          · cases' leg
            rename_i h1 h2 h3
            rw [List.cons_append]
            apply Chomp_law.cons
        · rw [if_neg q2]
          exact (Chomp_law_act_nz _ _ _ leg)
      · rw [if_neg q1] at leg


#exit



lemma preChomp_law_prop_law' (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) (act : ℕ × ℕ) (hist : List (ℕ × ℕ)) (hh : hist ≠ [])
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
  · rw [if_neg (show ¬ ((0, 0) ∈ Chomp_init height length ∧ (0, 0) ∉ hist ++ [(length, height)]) from (by intro con ; apply con.2 ; apply List.mem_append_left ;  rw [not_not] at q0 ; apply q0 ))]
    trivial


--#exit

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
