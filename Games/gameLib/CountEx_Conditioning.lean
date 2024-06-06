/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Conditioning_Symm



-- # Strong blindness but not hyper blindness

def transition (ini : ℕ) (hist : List ℕ) (_ : ℕ): ℕ :=
  if ini = 0
  then hist.dropLast.sum + 1
  else hist.sum + 1


def G : Symm_Game_World ℕ ℕ :=
  {init_game_state := 0
   win_states := fun n => n = 42
   law := fun _ _ _ => True
   transition := transition
   }

theorem strong_not_hyper :
  ∃ g : Symm_Game_World ℕ ℕ, g.strong_transition_blind ∧ (¬ g.hyper_transition_blind) :=
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
  · dsimp [Symm_Game_World.hyper_transition_blind, Symm_Game_World.hyper_transition_blind_fst, Symm_Game_World.hyper_transition_blind_snd]
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
      dsimp [G, transition, Symm_Game_World.world_after_preHist]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_pos (show 0 = 0 from by rfl)]
      rw [if_neg (show 0+1 ≠ 0 from by decide)]
      decide
