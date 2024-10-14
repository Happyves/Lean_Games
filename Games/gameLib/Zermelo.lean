
/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Games.gameLib.StrategyAPI


private lemma Game_World.has_WL_helper (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) :
  g.has_staged_WL hist leg → (¬ g.is_fst_staged_win hist leg) → g.is_snd_staged_win hist leg := by
  intro m c
  cases' m with m m
  · exfalso ; exact c m
  · exact m

private lemma Game_World.has_WL_helper' (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) :
  g.has_staged_WL hist leg → (¬ g.is_snd_staged_win hist leg) → g.is_fst_staged_win hist leg := by
  intro m c
  cases' m with m m
  · exact m
  · exfalso ; exact c m
