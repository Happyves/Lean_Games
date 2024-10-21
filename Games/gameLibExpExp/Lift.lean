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
      then g.snd_transition hist act
      else default
  }



lemma Game_World.lift_hist_neutral_of_cons (g : Game_World α β) [Inhabited α]
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {hist : List β} {act : β} (main : g.lift.hist_neutral (act :: hist)) :
  g.lift.hist_neutral ( hist) :=
  by
  constructor
  · intro ⟨pre,suf,win⟩
    apply main.not_fst
    use pre
    constructor
    · rw [List.suffix_cons_iff]
      right
      exact suf
    · exact win
  · intro ⟨pre,suf,win⟩
    apply main.not_snd
    use pre
    constructor
    · rw [List.suffix_cons_iff]
      right
      exact suf
    · exact win



lemma Game_World.lift_hist_neutral (g : Game_World α β) [Inhabited α]
   [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
   {hist : List β} (main : g.lift.hist_neutral hist) : g.hist_neutral hist :=
   by
   contrapose main
   have : g.fst_win_states hist ∨ g.snd_win_states hist  :=
      by by_contra hmm ; rw [not_or] at hmm ; apply main ⟨hmm.1, hmm.2 ⟩
   cases' this with F S
   · intro con
     apply con.not_fst
     use hist
     constructor
     · exact Exists.intro [] rfl
     · exact F
   · intro con
     apply con.not_snd
     use hist
     constructor
     · exact Exists.intro [] rfl
     · exact S

lemma Game_World.hist_neutral_lift (g : Game_World α β) [Inhabited α]
   [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
   {hist : List β} (main : g.hist_neutral hist) : g.lift.hist_neutral hist :=
   by
   contrapose main
   have : g.lift.fst_win_states hist ∨ g.lift.snd_win_states hist  :=
      by by_contra hmm ; rw [not_or] at hmm ; apply main ⟨hmm.1, hmm.2 ⟩
   cases' this with F S
   · intro con
     apply con.not_fst
     use hist
     constructor
     · exact Exists.intro [] rfl
     · exact F
   · intro con
     apply con.not_snd
     use hist
     constructor
     · exact Exists.intro [] rfl
     · exact S


#exit


lemma Game_World.lift_hist_legal (g : Game_World α β) [Inhabited α]
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {hist : List β} (main : g.lift.hist_legal hist) (N : g.lift.hist_neutral hist) : g.hist_legal hist :=
  by
  induction' hist with x l ih
  · apply Game_World.hist_legal.nil
  · cases' main
    rename_i sofar now
    split_ifs at now with T
    · apply Game_World.hist_legal.cons _ _ _ (ih sofar (g.lift_hist_neutral_of_cons N))
      rw [if_pos T]
      dsimp [lift] at now
      rwa [if_pos (g.lift_hist_neutral (g.lift_hist_neutral_of_cons N))] at now
    · apply Game_World.hist_legal.cons _ _ _ (ih sofar (g.lift_hist_neutral_of_cons N))
      rw [if_neg T]
      dsimp [lift] at now
      rwa [if_pos (g.lift_hist_neutral (g.lift_hist_neutral_of_cons N))] at now





def Game_World.liftFS (g : Game_World α β) [Inhabited α] [Inhabited β]
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  [DecidablePred (g.lift.fst_win_states) ] [ DecidablePred (g.lift.fst_win_states)]
  (fs : g.cfStrategy) : g.lift.fStrategy :=
  fun hist T leg =>
    if N : g.lift.hist_neutral hist
    then
      let ⟨v, p⟩ := fs hist T (g.lift_hist_legal leg N) (g.lift_hist_neutral N)
      sorry
    else ⟨default, (by dsimp [lift] ; rw [if_neg] ; )⟩
