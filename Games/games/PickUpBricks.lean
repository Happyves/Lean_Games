/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.Nat
import Games.gameLib.Basic
import Mathlib.Tactic


variable (init_bricks : ℕ)

def bricks_start_turn_from_ini_hist (ini : ℕ) (hist : List ℕ) := ini - hist.sum

def bricks_end_turn_from_ini_hist_act (ini : ℕ) (hist : List ℕ) (act : ℕ) := ini - hist.sum - act


def PickUpBricks : Symm_Game_World ℕ ℕ where
  init_game_state := init_bricks
  win_states := (fun n => n = 0)
  transition := bricks_end_turn_from_ini_hist_act init_bricks
  law := fun hist act => match (bricks_start_turn_from_ini_hist init_bricks hist) with
                             | 0 => act = 0
                             | 1 => act = 1
                             | _ => act = 1 ∨ act = 2


def pub_win_strat : List ℕ → ℕ  := -- for fst player ; (is strat ; remeber that init_bricks is section param)
  fun hist =>
    let b := bricks_start_turn_from_ini_hist init_bricks hist
    let d := b % 3
    if b = 0
    then 0
    else if d = 1 then 1 else 2


lemma pub_win_strat_legal : Game.strategy_legal init_bricks (PickUpBricks init_bricks).law pub_win_strat:=
  by
  dsimp [PickUpBricks, pub_win_strat]
  intro hist
  split
  · rename_i h
    dsimp [pub_win_strat]
    rw [if_pos h]
  · rename_i h
    dsimp [pub_win_strat]
    rw [if_neg _]
    <;> {rw [h] ; decide}
  · rename_i h1 h2
    dsimp [pub_win_strat]
    rw [if_neg _]
    · split_ifs <;> decide
    · apply h1


def toy_strat : List ℕ → ℕ  :=
  fun hist => if bricks_start_turn_from_ini_hist init_bricks hist = 0 then 0 else 1

lemma toy_strat_legal : Game.strategy_legal init_bricks (PickUpBricks init_bricks).law toy_strat:=
  by
  dsimp [PickUpBricks, pub_win_strat]
  intro hist
  split
  · rename_i h
    dsimp [toy_strat]
    rw [if_pos h]
  · rename_i h
    dsimp [toy_strat]
    rw [if_neg _]
    rw [h]
    decide
  · rename_i h1 h2
    dsimp [toy_strat]
    rw [if_neg _]
    · decide
    · apply h1


def PickUpBricks_pubWin_vs_toy : Symm_Game ℕ ℕ :=
  {(PickUpBricks 32) with
   fst_strat := pub_win_strat
   snd_strat := toy_strat
   fst_lawful := pub_win_strat_legal 32
   snd_lawful := toy_strat_legal 32}


#reduce Game.state_upto_turn' PickUpBricks_pubWin_vs_toy.toGame 30

set_option maxRecDepth 1000000 in
example : Game.state_on_turn' (PickUpBricks_pubWin_vs_toy.toGame) 21 = 0 := by decide
  -- bad performmence, O(turn^2), since recursion in `List.map` and `Game.state_on_turn`


example : PickUpBricks_pubWin_vs_toy.toGame.fst_win :=
  by
  rw [Game.fst_win]
  use 21
  constructor
  · decide
  · constructor
    · simp [Symm_Game.toGame, PickUpBricks_pubWin_vs_toy, PickUpBricks]
      decide
    · intro t tdef
      simp [Game.state_on_turn_neutral]
      interval_cases t
      all_goals {simp [Symm_Game.toGame, PickUpBricks_pubWin_vs_toy, PickUpBricks] ; decide}

#check Nat

lemma loop_invariant
  (win_hyp : init_bricks % 3 = 1 ∨ init_bricks % 3 = 2)
  (s_strat : Game.strategy ℕ ℕ)
  (s_law : Game.strategy_legal init_bricks (PickUpBricks init_bricks).law s_strat):
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := pub_win_strat
                             fst_lawful := pub_win_strat_legal init_bricks
                             snd_strat := s_strat
                             snd_lawful := s_law } ;
  ∀ turn, Game.turn_fst turn → (g.toGame.state_on_turn' turn) % 3 = 0 :=
  by
  intro g t
  apply @Nat.induct_2_step _ t
  · intro no
    rw [Game.turn_fst] at no
    contradiction
  · intro
    dsimp [g]
    dsimp [Symm_Game.toGame, Game.state_on_turn', Game.state_on_turn]
    rw [if_pos (by decide)]
    dsimp [Symm_Game_World.transition, PickUpBricks, Game.history_on_turn, bricks_end_turn_from_ini_hist_act, pub_win_strat, bricks_start_turn_from_ini_hist]
    split_ifs with z c
    · rw [z]
      decide
    · rw [Nat.sub_mod_eq_zero_of_mod_eq]
      apply c
    · rw [Nat.sub_mod_eq_zero_of_mod_eq]
      rw [or_comm ,or_iff_not_imp_right] at win_hyp
      exact win_hyp c
  · intro n ih0 ih1 tn
    rw [← Game.turn_fst_step] at tn
    specialize ih0 tn
    rw [Game.state_on_turn', Game.state_on_turn]
    split
    · contradiction
    · rename_i m hm
      -- rw [if_neg _]
      -- use ← Game.turn_snd_fst_step
      sorry



#exit

def pick_up_bricks_history (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ) : ℕ → List ℕ
| 0 => []
| (turn + 1) => if (turn % 2 = 0)
                then ((fst_strat bricks (pick_up_bricks_history bricks fst_strat  snd_strat turn)) :: (pick_up_bricks_history bricks fst_strat  snd_strat turn))
                else ((snd_strat bricks (pick_up_bricks_history bricks fst_strat  snd_strat turn)) :: (pick_up_bricks_history bricks fst_strat  snd_strat turn))


def numerology_strat (bricks : ℕ) (history : List ℕ) :=
 if ((Nat.Prime (List.length history)) ∧ ((bricks + (List.headD history 0)) % 2 = 1))
 then 2
 else 1

def win_strat (bricks : ℕ) (history : List ℕ) :=
  if ((bricks - history.sum ) % 3) = 1 then 1 else 2

def pick_up_bricks_state (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ) (turn : ℕ) :=
  bricks - (pick_up_bricks_history bricks fst_strat snd_strat turn).sum

def pick_up_bricks_state_history (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ) (turn : ℕ) :=
 List.map (fun t => pick_up_bricks_state bricks fst_strat snd_strat t) (List.range (turn + 1))

#eval pick_up_bricks_state_history 10 numerology_strat numerology_strat 5
#eval pick_up_bricks_state_history 10 numerology_strat numerology_strat 10
#eval pick_up_bricks_state_history 10 numerology_strat numerology_strat 20

#eval pick_up_bricks_state_history 10 win_strat numerology_strat 5
#eval pick_up_bricks_state_history 10 win_strat numerology_strat 10
#eval pick_up_bricks_state_history 10 win_strat numerology_strat 20

def strat_stealing_strat (bricks : ℕ) (history : List ℕ) :=
  List.headD history 1

#eval pick_up_bricks_state_history 20 win_strat strat_stealing_strat 5
#eval pick_up_bricks_state_history 20 win_strat strat_stealing_strat 10
#eval pick_up_bricks_state_history 20 win_strat strat_stealing_strat 20

#eval pick_up_bricks_history 20 win_strat strat_stealing_strat 20
  -- history of actions: note that the odd actions are always equal to the prevous action
  -- that's startegy stealing


def legal_strat (strat :  ℕ → (List ℕ) → ℕ) : Prop :=
  ∀ bricks : ℕ, ∀ history : List ℕ, ((strat bricks history = 1 ) ∨ (strat bricks history = 2))
  -- tecnically on should check that there are enough bricks to pick up
  -- but with subtraction on nat, this trns out to be fine
  -- Note: the current number of bricks is (bricks - history.sum)
  -- Adding bricks as parameter would complicate things in the inductions to come.



lemma termination_pre (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ)
                      (hf : legal_strat fst_strat) (hs : legal_strat snd_strat):
      ∀ turn : ℕ, (pick_up_bricks_state bricks fst_strat snd_strat (turn+1) < pick_up_bricks_state bricks fst_strat snd_strat turn)
                  ∨ (pick_up_bricks_state bricks fst_strat snd_strat (turn + 1) = 0) :=
  by
  intro turn
  rw [or_iff_not_imp_right]
  intro non_zero
  simp [pick_up_bricks_state, pick_up_bricks_history] at *
  simp [legal_strat] at hf
  simp [legal_strat] at hs
  specialize hf bricks (pick_up_bricks_history bricks fst_strat snd_strat turn)
  specialize hs bricks (pick_up_bricks_history bricks fst_strat snd_strat turn)
  split_ifs with h
  · simp
    cases' hf with hf hf
    · rw [hf]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_pos h] at non_zero
      simp at non_zero
      rw [hf] at non_zero
      linarith
    · rw [hf]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_pos h] at non_zero
      simp at non_zero
      rw [hf] at non_zero
      linarith
  · simp
    cases' hs with hs hs
    · rw [hs]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_neg h] at non_zero
      simp at non_zero
      rw [hs] at non_zero
      linarith
    · rw [hs]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_neg h] at non_zero
      simp at non_zero
      rw [hs] at non_zero
      linarith





lemma termination (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ)
                  (hf : legal_strat fst_strat) (hs : legal_strat snd_strat):
      ∃ turn : ℕ,  pick_up_bricks_state bricks fst_strat snd_strat turn = 0
      :=
  by
  apply Nat.well_ordered
  intro n
  rw [or_iff_not_imp_right]
  intro nz
  simp [pick_up_bricks_state, pick_up_bricks_history] at nz
  dsimp [legal_strat] at hf
  dsimp [legal_strat] at hs
  simp [pick_up_bricks_state, pick_up_bricks_history]
  specialize hf bricks (pick_up_bricks_history bricks fst_strat snd_strat n)
  specialize hs bricks (pick_up_bricks_history bricks fst_strat snd_strat n)
  rw [tsub_lt_tsub_iff_left_of_le]
  split_ifs with h
  · rw [List.sum_cons]
    cases' hf with hf hf
    · linarith
    · linarith
  · rw [List.sum_cons]
    cases' hs with hs hs
    · linarith
    · linarith
  apply le_of_lt
  exact nz

lemma win_strat_legal : legal_strat win_strat :=
  by
  dsimp [legal_strat]
  intro b h
  dsimp [win_strat]
  split_ifs with H
  left
  rfl
  right
  rfl
