/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic
import Games.gameLib.Zermelo_Symm





def zSymm_Game_World.world_after_preHist {α β : Type u} (g : zSymm_Game_World α β)
  (prehist : List β) : zSymm_Game_World α β := -- act not required to be legal
  match prehist with
  | [] => g
  | last :: L => {(g.toSymm_Game_World.world_after_preHist prehist) with
                      law_careless :=
                          by
                          cases' prehist with ph
                          · dsimp [Symm_Game_World.world_after_preHist]
                            apply g.law_careless
                          · dsimp [Symm_Game_World.world_after_preHist]
                            apply g.law_careless
                      transition_careless :=
                          by
                          cases' prehist with ph
                          · dsimp [Symm_Game_World.world_after_preHist]
                            apply g.transition_careless
                          · dsimp [Symm_Game_World.world_after_preHist]
                            apply g.transition_careless
                      coherent := by
                                  intro f_strat s_strat t
                                  intro fws
                                  dsimp at *
                                  sorry
                      playable :=
                            by
                            cases' prehist with ph
                            · dsimp [Symm_Game_World.world_after_preHist]
                              apply g.playable
                            · dsimp [Symm_Game_World.world_after_preHist]
                              apply g.playable
                                  }

  --{g with init_game_state := g.transition g.init_game_state L last }

def Stealing_condition (g : zSymm_Game_World α β)
  (f_act s_act : β)
  (f_leg : g.law g.init_game_state [] f_act) (s_leg : g.law g.init_game_state [f_act] s_act):
  Prop := ∃ f_steal : β, g.world_after_preHist [s_act, f_act] = g.world_after_fst f_act f_leg
