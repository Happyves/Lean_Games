/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic
import Games.gameLib.Zermelo_Symm
import Mathlib.Data.List.DropRight


def strat_predeco (strat : Strategy α β) (prehist : List β) (g : Symm_Game_World α β) : Strategy α β :=
  (fun _ hist => if s : hist.length < prehist.length then prehist.reverse.get ⟨hist.length, (by rw [List.length_reverse] ; exact s)⟩  else strat (g.world_after_preHist prehist).init_game_state (hist.rdrop prehist.length))



lemma Symm_Game_World.History_of_predeco_len_prehist
  (g: Symm_Game_World α β)
  (prehist: List β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := strat_predeco s_strat prehist g
  let snd_strat := strat_predeco f_strat prehist g
  History_on_turn g.init_game_state fst_strat snd_strat (prehist.length) = prehist :=
  by
  induction' prehist with x l ih
  · dsimp [History_on_turn]
  · dsimp at *
    dsimp [History_on_turn]
    by_cases q : Turn_fst (List.length l + 1)
    · rw [if_pos q]
      dsimp [strat_predeco]
      simp_rw [History_on_turn_length]
      rw [dif_pos (by exact Nat.lt.base (List.length l))]
      have := List.reverse_cons x l
      simp_rw [this]


#exit

lemma Symm_Game_World.History_of_predeco
  (g: Symm_Game_World α β)
  (prehist: List β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := strat_predeco s_strat prehist g
  let snd_strat := strat_predeco f_strat prehist g
  History_on_turn g.init_game_state fst_strat snd_strat (turn + prehist.length) =
  (History_on_turn (g.world_after_preHist prehist).init_game_state f_strat s_strat turn) ++ prehist :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [History_on_turn]

  · sorry

#exit


lemma Symm_Game_World.state_world_after_preHist (g : Symm_Game_World α β)
  (prehist : List β) (fst_strat snd_strat : Strategy α β) (t : ℕ) :
  (g.world_after_preHist prehist).state_on_turn fst_strat snd_strat t =
  (g.state_on_turn (strat_predeco fst_strat) (strat_predeco snd_strat) t):=
  by




#exit

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
                                  have := g.coherent
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
