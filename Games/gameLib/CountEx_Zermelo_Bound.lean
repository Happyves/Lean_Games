/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Conditioning_wDraw
import Games.gameLib.Termination
import Mathlib.Tactic


def G : Game_World_wDraw ℕ ℕ :=
  {init_game_state := 0
   fst_win_states := fun x => x = 42
   snd_win_states := fun x => x = 42
   draw_states := fun x => x = 42
   fst_legal := fun ini _ act => -- law changes depending on initial state ; should also break Zermelo
      if ini = 1
      then act = 0
      else act = 1
   snd_legal := fun ini _ act =>
      if ini = 1
      then act = 0
      else act = 1
   fst_transition := fun ini hist act => ini + hist.sum + act
   snd_transition := fun ini hist act => ini + hist.sum + act
  }


example :
  ∃ (g : Game_World_wDraw ℕ ℕ),
  ∃ T : ℕ, ∃ (hg : g.isWLD_wBound (T + 1)),
  ∃ (fst_act : ℕ), ∃  (leg : g.fst_legal g.init_game_state [] fst_act),
  ¬ (g.world_after_fst fst_act).isWLD_wBound T :=
  by
  use G
  use 41

  have : G.isWLD_wBound 42 :=
    by
    intro f_strat s_strat f_leg s_leg
    use 42
    constructor
    · apply le_refl
    · apply Game_World_wDraw.Turn_isWLD.ws
      · decide
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
        have that : ∀ n : ℕ, Game_World_wDraw.state_on_turn G f_strat s_strat n = n :=
          by
          intro n
          induction' n with n ih
          · dsimp [G, Game_World_wDraw.state_on_turn]
          · unfold Game_World_wDraw.state_on_turn
            dsimp
            split_ifs
            · rename_i tf
              dsimp [G, Game_World_wDraw.history_on_turn]
              specialize f_leg n tf
              dsimp [G] at f_leg
              rw [if_neg (by decide)] at f_leg
              rw [f_leg, this]
              norm_num
            · rename_i tf
              dsimp [G, Game_World_wDraw.history_on_turn]
              specialize s_leg n tf
              dsimp [G] at s_leg
              rw [if_neg (by decide)] at s_leg
              rw [s_leg, this]
              norm_num
        clear this
        rw [that]
        dsimp [G]

  use this
  clear this
  use 1
  use (by dsimp [G] ; rw [if_neg (by decide)])
  unfold Game_World_wDraw.isWLD_wBound
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
      have that : ∀ n : ℕ, Game_World_wDraw.state_on_turn (G.world_after_fst 1) (fun _ _ => 0) (fun _ _ => 0) n = 1 :=
          by
          intro n
          induction' n with n ih
          · dsimp [G, Game_World_wDraw.state_on_turn]
          · dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn]
            split_ifs
            · dsimp [G]
              rw [this]
            · dsimp [G]
              rw [this]

      cases' con with tf fw ts sw d
      · dsimp [G] at fw that
        rw [that t] at fw
        norm_num at fw
      · dsimp [G] at sw that
        rw [that t] at sw
        norm_num at sw
      · dsimp [G] at d that
        rw [that t] at d
        norm_num at d



/-
In zermelos proof, when we use backward induction, we assum that making the move
will not affect the game, so that we may play with its strategies, but we may build
game where the first move influences that moves that are legal afterwards, so that
the game may not be the same afterwards
-/
