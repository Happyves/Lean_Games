/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExp.Basic


inductive Game_World.hist_on_turn_valid (g : Game_World α β) {t : Nat} : g.hist_on_turn_output t → Prop
| ofTerminal (result : {hist : List β // g.hist_legal hist ∧ hist.length = t}) : g.hist_on_turn_valid (.terminal result)
| ofNonterminal (result : {hist : List β // g.hist_legal hist ∧ hist.length = t}) (property : g.hist_neutral result.val) : g.hist_on_turn_valid (.nonterminal result property)


lemma Game_World.hist_on_turn_valid_not_invalid (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  g.hist_on_turn fst_strat snd_strat t ≠ Game_World.hist_on_turn_output.invalid :=
  match Q : g.hist_on_turn fst_strat snd_strat t with
  | .invalid => by rw [Q] at V ; cases V
  | .terminal _ => Game_World.hist_on_turn_output.noConfusion
  | .nonterminal _ _ => Game_World.hist_on_turn_output.noConfusion


def Game_World.hist_on_turn_value (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  List β :=
  match Q : g.hist_on_turn fst_strat snd_strat t with
  | .invalid => False.elim ((g.hist_on_turn_valid_not_invalid _ _ _ V) Q)
  | .terminal res => res.val
  | .nonterminal res _ => res.val


lemma Game_World.hist_on_turn_value_length (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  (g.hist_on_turn_value fst_strat snd_strat t V).length = t :=
  match Q : g.hist_on_turn fst_strat snd_strat t with
  | .invalid => False.elim ((g.hist_on_turn_valid_not_invalid _ _ _ V) Q)
  | .terminal _ | .nonterminal _ _ => by
      dsimp [Game_World.hist_on_turn_value]
      split
      · contradiction
      · rename_i res' _
        apply res'.prop.2
      · rename_i res' _ _
        apply res'.prop.2


lemma Game_World.hist_on_turn_value_legal (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  g.hist_legal (g.hist_on_turn_value fst_strat snd_strat t V) :=
  match Q : g.hist_on_turn fst_strat snd_strat t with
  | .invalid => False.elim ((g.hist_on_turn_valid_not_invalid _ _ _ V) Q)
  | .terminal _ | .nonterminal _ _ => by
      dsimp [Game_World.hist_on_turn_value]
      split
      · contradiction
      · rename_i res' _
        apply res'.prop.1
      · rename_i res' _ _
        apply res'.prop.1
