/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic


def PosGameW_trans [DecidableEq α] (player : Fin 3) (hist : List α) (act : α) : α → Fin 3 :=
  fun p => if h1 : p = act
           then player
           else if h2 : p ∈ hist
                then if h2a : Turn_fst (hist.indexOf p)
                     then 1
                     else 2
                else 0



def Positional_Game_World [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : Game_World (α → Fin 3) α where
  init_game_state := fun _ => 0 -- initially, none of the board has calimed tiles
  fst_win_states := fun s => ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => s x = 1) Finset.univ
  fst_transition := fun hist act => PosGameW_trans 1 hist act
  fst_legal := fun hist act => act ∉ hist
  snd_win_states := fun s => ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => s x = 2) Finset.univ
  snd_transition := fun hist act => PosGameW_trans 2 hist act
  snd_legal := fun hist act => act ∉ hist
