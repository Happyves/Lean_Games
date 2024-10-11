/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExp.HistoryAPI




def Game_World.Turn_isWL (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  ∃ result : {hist : List β // g.hist_legal hist ∧ hist.length = turn},
    g.hist_on_turn f_strat s_strat turn = .terminal result

def Symm_Game_World.Turn_isWL (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  ∃ result : {hist : List β // g.hist_legal hist ∧ hist.length = turn},
    g.hist_on_turn f_strat s_strat turn = .terminal result


lemma Game_World.hist_valid_of_turn_isWL (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {f_strat : g.fStrategy} {s_strat : g.sStrategy} {turn : ℕ}
  (h : g.Turn_isWL f_strat s_strat turn) :
  g.hist_on_turn_valid (g.hist_on_turn f_strat s_strat turn) :=
  by
  obtain ⟨res, res_eq⟩ := h
  rw [res_eq]
  apply Game_World.hist_on_turn_valid.ofTerminal res

lemma Symm_Game_World.hist_valid_of_turn_isWL (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {f_strat : g.fStrategy} {s_strat : g.sStrategy} {turn : ℕ}
  (h : g.Turn_isWL f_strat s_strat turn) :
  g.hist_on_turn_valid (g.hist_on_turn f_strat s_strat turn) :=
  by convert @Game_World.hist_valid_of_turn_isWL _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) f_strat s_strat turn (by apply h)


def Game_World.isWL (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]: Prop :=
  ∀ (f_strat : g.fStrategy), ∀ (s_strat : g.sStrategy),
  ∃ turn, g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.isWL (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]: Prop :=
  @Game_World.isWL _ _  (g.toGame_World) (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win])


def Game_World.state_on_turn_neutral (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ)  : Prop :=
  ¬ g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.state_on_turn_neutral (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  @Game_World.state_on_turn_neutral _ _  (g.toGame_World) (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) f_strat s_strat turn

def Game.state_on_turn_neutral (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (turn : ℕ) : Prop :=
  g.toGame_World.state_on_turn_neutral g.fst_strat g.snd_strat turn

def Symm_Game.state_on_turn_neutral (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (turn : ℕ) : Prop :=
  @Game.state_on_turn_neutral _ _ g.toGame (by rwa [g.toGame_fst_win]) (by rwa [g.toGame_snd_win]) turn


def Game.fst_win (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  ∃ turn : ℕ, ∃ V : g.Turn_isWL g.fst_strat g.snd_strat turn,
    let H := g.hist_on_turn_value turn (g.hist_valid_of_turn_isWL V)
    g.fst_win_states H ∧ (∀ t < turn, g.state_on_turn_neutral t)

def Game.snd_win (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  ∃ turn : ℕ, ∃ V : g.Turn_isWL g.fst_strat g.snd_strat turn,
    let H := g.hist_on_turn_value turn (g.hist_valid_of_turn_isWL V)
    g.snd_win_states H ∧ (∀ t < turn, g.state_on_turn_neutral t)

def Symm_Game.fst_win (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  @Game.fst_win _ _ g.toGame (by rwa [g.toGame_fst_win]) (by rwa [g.toGame_snd_win])

def Symm_Game.snd_win (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  @Game.snd_win _ _ g.toGame (by rwa [g.toGame_fst_win]) (by rwa [g.toGame_snd_win])



def Game_World.is_fst_win (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  ∃ ws : g.fStrategy, ∀ snd_s : g.sStrategy,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game α β).fst_win

def Game_World.is_snd_win (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  ∃ ws : g.sStrategy, ∀ snd_s : g.fStrategy,
  ({g with snd_strat := ws, fst_strat := snd_s} : Game α β).fst_win

def Symm_Game_World.is_fst_win (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  @Game_World.is_fst_win _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win])

def Symm_Game_World.is_snd_win (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]: Prop :=
  @Game_World.is_snd_win _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win])

inductive Game_World.has_WL (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop where
  | wf (h : g.is_fst_win)
  | ws (h : g.is_snd_win)

def Symm_Game_World.has_WL (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] :=
  @Game_World.has_WL _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win])


lemma Game_World.Turn_isWL_wins (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {f_strat : g.fStrategy} {s_strat : g.sStrategy} {turn : ℕ}
  (h : g.Turn_isWL f_strat s_strat turn) :
  g.fst_win_states (g.hist_on_turn_value f_strat s_strat turn (g.hist_valid_of_turn_isWL h))
  ∨ g.snd_win_states (g.hist_on_turn_value  f_strat s_strat turn (g.hist_valid_of_turn_isWL h)) :=
  by
  obtain ⟨_,q⟩ := h
  have : ¬ g.hist_neutral (g.hist_on_turn_value f_strat s_strat turn (g.hist_valid_of_turn_isWL h)) := by
    intro con
    cases' turn with t
    · dsimp [hist_on_turn] at q
      rw [Game_World.hist_on_turn_value_zero] at con
      rw [dif_pos con] at q
      contradiction
    ·
