/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.Nat
import Games.gameLib.Basic
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

variable (height length : ℕ)

-- pretty print the state
def pp_Chomp_state (l : List (ℕ × ℕ)) :=
  ((List.range (length)) ×ˢ (List.range (height))).filter
    (fun p => ∀ q ∈ l, nondomi q p)

structure Chomp_law (_ : List (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  h : act.2 ≤ height
  l : act.1 ≤ length
  nd : pp_Chomp_state height length hist ≠ [(0,0)] → ∀ q ∈ hist, nondomi q act
  nz : act ≠ (0,0) -- even when end is reached, the partial function phenomenon forbids playing (0,0)
  -- for the game to be playable, one of `height` or `length` must be positive

def Chomp : Symm_Game_World (List (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := (pp_Chomp_state height length) []
  win_states := (fun state => state = [(0,0)])
  transition := fun _ hist act => if (pp_Chomp_state height length hist) = [(0,0)]
                                    then [(0,0)]
                                    else (pp_Chomp_state height length) (act :: hist)
  law := Chomp_law height length


lemma Chomp_law_careless : careless (Chomp height length).law (Chomp height length).transition :=
  by
  intro ini hist prehist Hpre
  dsimp [Chomp]
  ext






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
