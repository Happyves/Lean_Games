/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.HistoryAPI
import Games.gameLib.Termination

lemma Game_World.state_on_turn_eq_state_from_hist (g : Game_World α β)
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

def State_from_history (ini : α ) (f_trans s_trans : List β → (β → α)) : List β → α
| [] => ini
| a :: h => if Turn_fst (h.length +1)
            then f_trans h a
            else s_trans h a

lemma Game_World.state_on_turn_State_from_history (g : Game_World α β)
    (fst_strat : g.fStrategy) (snd_strat : g.sStrategy)
    (t : ℕ) :
    g.state_on_turn fst_strat snd_strat t =
    State_from_history g.init_game_state g.fst_transition g.snd_transition
    (g.hist_on_turn fst_strat snd_strat t).val :=
    by
    cases' t with t
    · dsimp!
    · dsimp [state_on_turn, hist_on_turn]
      split_ifs with T
      · dsimp [State_from_history]
        simp_rw [hist_on_turn_length]
        rw [if_pos T]
      · dsimp [State_from_history]
        simp_rw [hist_on_turn_length]
        rw [if_neg T]


def State_from_history_neutral_wDraw (ini : α ) (f_wins s_wins draw : List β → Prop) (hist : List β) : Prop :=
  (¬ (f_wins hist)) ∧ (¬ (s_wins hist) ∧ (¬ (draw hist)))


lemma Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral (g : Game_World_wDraw α β)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) :
  g.state_on_turn_neutral f_strat s_strat turn ↔
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states
  (g.hist_on_turn f_strat s_strat turn).val :=
  by
  dsimp [Game_World_wDraw.state_on_turn_neutral, State_from_history_neutral_wDraw]
  rw [← not_or, ← not_or, not_iff_not]
  constructor
  · intro h
    cases' h with F S D
    · left ; exact F
    · right ; left ; exact S
    · right ; right ; exact D
  · intro h
    cases' h with F O
    · apply Game_World_wDraw.Turn_isWLD.wf ; exact F
    · cases' O with S D
      · apply Game_World_wDraw.Turn_isWLD.ws ; exact S
      · apply Game_World_wDraw.Turn_isWLD.drw ; exact D
