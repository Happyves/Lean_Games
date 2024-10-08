/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.HistoryAPI


lemma Game_World.state_on_turn_eq_state_from_hist (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} :
  g.state_on_turn fst_strat snd_strat t = g.state_from_hist (g.hist_on_turn fst_strat snd_strat t) :=
  by
  cases' t with t
  · dsimp!
  · dsimp [state_on_turn, hist_on_turn]
    split_ifs with T
    · dsimp [state_from_hist]
      simp_rw [hist_on_turn_length]
      rw [if_pos T]
    · dsimp [state_from_hist]
      simp_rw [hist_on_turn_length]
      rw [if_neg T]
