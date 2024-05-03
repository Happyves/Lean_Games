/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Conditioning_wDraw



-- # Strong blindness but not hyper blindness

def transition (ini : ℕ) (hist : List ℕ) (_ : ℕ): ℕ :=
  if ini = 0
  then hist.dropLast.sum + 1
  else hist.sum + 1


def G : Game_World_wDraw ℕ ℕ :=
  {init_game_state := 0
   fst_win_states := fun n => n = 42
   snd_win_states := fun n => n = 42
   fst_legal := fun _ _ _ => True
   snd_legal := fun _ _ _ => True
   fst_transition := transition
   snd_transition := transition
   draw_states := fun n => n = 42
   }

theorem strong_not_hyper :
  ∃ g : Game_World_wDraw ℕ ℕ, g.strong_transition_blind ∧ (¬ g.hyper_transition_blind) :=
  by
  use G
  constructor
  · constructor
    · intro f_act _ hist act
      dsimp [G, transition]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_neg (show 0+1 ≠ 0 from by decide)]
      rw [List.dropLast_concat]
    · intro f_act _ hist act
      dsimp [G, transition]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_neg (show 0+1 ≠ 0 from by decide)]
      rw [List.dropLast_concat]
  · dsimp [Game_World_wDraw.hyper_transition_blind, Game_World_wDraw.hyper_transition_blind_fst, Game_World_wDraw.hyper_transition_blind_snd]
    push_neg
    intro _
    use [1,2]
    constructor
    · apply Hist_legal.cons
      · dsimp
        rw [if_neg (by decide)]
        dsimp [G]
      · apply Hist_legal.cons
        · dsimp
          rw [if_pos (by decide)]
          dsimp [G]
        · apply Hist_legal.nil
    · use []
      use 42
      dsimp [G, transition, Game_World_wDraw.world_after_preHist]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_neg (show 0+1 ≠ 0 from by decide)]
      decide
