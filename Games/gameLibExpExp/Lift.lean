/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExpExp.Basic
import Games.gameLib.Basic


def Game_World.lift (g : Game_World α β) [Inhabited α]
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  : Game_World α β :=
  {init_game_state := g.init_game_state
   fst_win_states := fun hist => ∃ pre, pre <:+ hist ∧ g.fst_win_states pre
   snd_win_states := fun hist => ∃ pre, pre <:+ hist ∧ g.snd_win_states pre
   fst_legal := fun hist act =>
      if g.hist_neutral hist
      then g.fst_legal hist act
      else True
   snd_legal := fun hist act =>
      if g.hist_neutral hist
      then g.snd_legal hist act
      else True
   fst_transition := fun hist act =>
      if g.hist_neutral hist
      then g.fst_transition hist act
      else default
   snd_transition := fun hist act =>
      if g.hist_neutral hist
      then g.fst_transition hist act
      else default
  }

def Game_World.liftFS (g : Game_World α β) [Inhabited α]
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fs : g.cfStrategy) : g.lift.fStrategy :=
  fun hist T leg =>
    if N : g.hist_neutral hist
    then fs hist T leg N
    else sorry
