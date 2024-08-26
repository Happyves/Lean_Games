/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Termination


def PosGame_trans [DecidableEq α] (hist : List α) : α → Fin 3 :=
  fun p => if  p ∈ hist
           then if Turn_fst (hist.indexOf p)
                then 1
                else 2
           else 0


structure Positional_Game_World [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) extends Game_World_wDraw (α → Fin 3) α where
     init_scheme : toGame_World_wDraw.init_game_state = fun _ => 0
     fst_win_states_scheme : ∀ hist, Hist_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal (hist) →
                                   (toGame_World_wDraw.fst_win_states toGame_World_wDraw.init_game_state hist ↔ (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_transition toGame_World_wDraw.snd_transition hist) x = 1) Finset.univ))
     snd_win_states_scheme : ∀ hist, Hist_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal (hist) →
                                   (toGame_World_wDraw.snd_win_states toGame_World_wDraw.init_game_state hist ↔ (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_transition toGame_World_wDraw.snd_transition hist) x = 2) Finset.univ))
     legal_condition : ∀ hist, ∀ act, Hist_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal (act :: hist) →
                              (State_from_history_neutral_wDraw toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_win_states toGame_World_wDraw.snd_win_states toGame_World_wDraw.draw_states hist) →
                                   act ∉ hist
     transition_scheme : ∀ hist, Hist_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal (hist) →
                              State_from_history toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_transition toGame_World_wDraw.snd_transition hist = PosGame_trans hist
