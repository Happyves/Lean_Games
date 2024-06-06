/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Conditioning_Symm
import Games.gameLib.Termination
import Mathlib.Tactic


def G : Symm_Game_World ℕ ℕ :=
  {init_game_state := 0
   win_states := fun x => x = 42
   law := fun ini _ act => -- law changes depending on initial state ; should also break Zermelo
      if ini = 1
      then act = 0
      else act = 1
   transition := fun ini hist act => ini + hist.sum + act
  }


example :
  ∃ (g : Symm_Game_World ℕ ℕ),
  ∃ T : ℕ, ∃ (hg : g.isWL_wBound (T + 1)),
  ∃ (fst_act : ℕ), ∃  (leg : g.law g.init_game_state [] fst_act),
  ¬ (g.world_after_fst fst_act).isWL_wBound T :=
  by
  use G
  use 41

  have : G.isWL_wBound 42 :=
    by
    intro f_strat s_strat f_leg s_leg
    use 42
    constructor
    · apply le_refl
    -- · apply Symm_Game_World.Turn_isWL
    --   · decide
    · have : ∀ n : ℕ, (History_on_turn 0 f_strat s_strat n).sum = n :=
        by
        intro n
        induction' n with n ih
        · dsimp [History_on_turn]
        · dsimp [History_on_turn]
          split_ifs
          · rename_i tf
            specialize f_leg n tf
            dsimp [G] at f_leg
            rw [if_neg (by decide)] at f_leg
            rw [f_leg, List.sum_cons, ih, add_comm]
          · rename_i tf
            specialize s_leg n tf
            dsimp [G] at s_leg
            rw [if_neg (by decide)] at s_leg
            rw [s_leg, List.sum_cons, ih, add_comm]
      have that : ∀ n : ℕ, Symm_Game_World.state_on_turn G f_strat s_strat n = n :=
        by
        intro n
        induction' n with n ih
        · dsimp [G, Symm_Game_World.state_on_turn]
        · unfold Symm_Game_World.state_on_turn
          dsimp
          split_ifs
          · rename_i tf
            dsimp [G, Symm_Game_World.history_on_turn]
            specialize f_leg n tf
            dsimp [G] at f_leg
            rw [if_neg (by decide)] at f_leg
            rw [f_leg, this]
            norm_num
          · rename_i tf
            dsimp [G, Symm_Game_World.history_on_turn]
            specialize s_leg n tf
            dsimp [G] at s_leg
            rw [if_neg (by decide)] at s_leg
            rw [s_leg, this]
            norm_num
      clear this
      dsimp [Symm_Game_World.Turn_isWL ]
      rw [that]
      dsimp [G]

  use this
  clear this
  use 1
  use (by dsimp [G] ; rw [if_neg (by decide)])
  unfold Symm_Game_World.isWL_wBound
  push_neg
  use (fun _ _ => 0)
  use (fun _ _ => 0)
  constructor
  · dsimp [G]
    intro t tf
    rw [if_pos (by decide)]
  · constructor
    · dsimp [G]
      intro t tf
      rw [if_pos (by decide)]
    · intro t tbd con
      have : ∀ n : ℕ, (History_on_turn 1 (fun _ _ => 0) (fun _ _ => 0) n).sum = 0 :=
        by
        intro n
        induction' n with n ih
        · dsimp [History_on_turn]
        · dsimp [History_on_turn]
          split_ifs
          · rw [List.sum_cons, ih]
          · rw [List.sum_cons, ih]
      have that : ∀ n : ℕ, Symm_Game_World.state_on_turn (G.world_after_fst 1) (fun _ _ => 0) (fun _ _ => 0) n = 1 :=
          by
          intro n
          induction' n with n ih
          · dsimp [G, Symm_Game_World.state_on_turn]
          · dsimp [Symm_Game_World.state_on_turn, Symm_Game_World.history_on_turn]
            split_ifs
            · dsimp [G]
              rw [this]
            · dsimp [G]
              rw [this]

      dsimp [G, Symm_Game_World.Turn_isWL] at *
      rw [that t]  at con
      norm_num at con




/-
In zermelos proof, when we use backward induction, we assum that making the move
will not affect the game, so that we may play with its strategies, but we may build
game where the first move influences that moves that are legal afterwards, so that
the game may not be the same afterwards
-/
