/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.HistoryAPI


variable (init_bricks : ℕ) -- the initial number of bricks as a variable

/--
Given an initial number of bricks and a history of bricks taken, return the current number of bricks.
-/
def bricks_from_ini_hist (ini : ℕ) (hist : List ℕ) := ini - hist.sum

/--
Given an initial number of bricks, a history of bricks taken and the current number of bricks
being taken, return the current number of bricks.
-/
def bricks_from_ini_hist_act (ini : ℕ) (hist : List ℕ) (act : ℕ) := ini - hist.sum - act


lemma bricks_cons (ini : ℕ) (hist : List ℕ) (x : ℕ) :
  bricks_from_ini_hist ini (x :: hist) = bricks_from_ini_hist ini hist - x :=
  by
  dsimp [bricks_from_ini_hist]
  rw [List.sum_cons]
  rw [add_comm, Nat.sub_add_eq]


def PickUpBricks : Symm_Game_World ℕ ℕ where
  init_game_state := init_bricks
  fst_win_states := (fun hist => bricks_from_ini_hist init_bricks hist = 0) -- won once no bricks left
  snd_win_states := (fun hist => bricks_from_ini_hist init_bricks hist = 0)
  transition :=  bricks_from_ini_hist_act init_bricks
  law := fun hist act =>  let B := (bricks_from_ini_hist init_bricks hist)
                              if B = 0
                              then act = 0
                              else  if B = 1
                                    then act = 1
                                    else act = 1 ∨ act = 2

instance : DecidablePred (PickUpBricks init_bricks).fst_win_states := by
  intro hist
  dsimp [PickUpBricks, bricks_from_ini_hist]
  exact Nat.decEq (init_bricks - List.sum hist) 0

instance : DecidablePred (PickUpBricks init_bricks).snd_win_states := by
  intro hist
  dsimp [PickUpBricks, bricks_from_ini_hist]
  exact Nat.decEq (init_bricks - List.sum hist) 0



def pub_win_strat : (PickUpBricks init_bricks).sStrategy :=
  fun hist _ _ =>
    let B := bricks_from_ini_hist init_bricks hist
    if Z : B = 0
    then ⟨0, (by dsimp [PickUpBricks] ; dsimp [B] at Z ; rw [Z, if_pos rfl])⟩
    else  if M : B % 3 = 1
          then ⟨1, (by dsimp [PickUpBricks] ; dsimp [B] at Z M ; rw [if_neg Z] ; split_ifs ; rfl ; left ; rfl)⟩
          else ⟨2, (by dsimp [PickUpBricks] ; dsimp [B] at Z M ; rw [if_neg Z] ; rw [if_neg (by contrapose! M ; rw [M] ; decide)] ; right ; rfl )⟩


def toy_strat : (PickUpBricks init_bricks).fStrategy :=
  fun hist _ _ =>
    let B := bricks_from_ini_hist init_bricks hist
    if Z : B = 0
    then ⟨0, (by dsimp [PickUpBricks] ; dsimp [B] at Z ; rw [Z, if_pos rfl])⟩
    else ⟨1, (by dsimp [PickUpBricks] ; dsimp [B] at Z ; rw [if_neg Z] ; split_ifs ; rfl ; left ; rfl)⟩


/--
Pick up bricks played with 32 initial bricks, with the winning strat as
first strat and the toy strat as second strat
-/
def PickUpBricks_pubWin_vs_toy : Symm_Game ℕ ℕ :=
  {(PickUpBricks 37) with
   fst_strat := toy_strat 37
   snd_strat := pub_win_strat 37
  }


instance : DecidablePred (PickUpBricks_pubWin_vs_toy).fst_win_states := by
  intro hist
  dsimp [PickUpBricks_pubWin_vs_toy]
  apply instDecidablePredListNatFst_win_statesPickUpBricks

instance : DecidablePred (PickUpBricks_pubWin_vs_toy).snd_win_states := by
  intro hist
  dsimp [PickUpBricks_pubWin_vs_toy]
  apply instDecidablePredListNatFst_win_statesPickUpBricks


#eval (PickUpBricks_pubWin_vs_toy.hist_on_turn 30).val.reverse
#eval (List.range 30).map (PickUpBricks_pubWin_vs_toy.state_on_turn)


lemma loop_invariant
  (win_hyp : 3 ∣ init_bricks)
  (f_strat : (PickUpBricks init_bricks).fStrategy) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             snd_strat := pub_win_strat init_bricks
                            } ;
  ∀ turn, Turn_snd turn → 3 ∣ bricks_from_ini_hist init_bricks (g.hist_on_turn turn) :=
  by
  intro g t T
  apply Invariant_snd _ _ t T
  · dsimp [bricks_from_ini_hist, Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
    exact win_hyp
  · intro t T ih
    rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn_2step_snd _ _ _ T, bricks_from_ini_hist]
    rw [List.sum_cons, List.sum_cons]
