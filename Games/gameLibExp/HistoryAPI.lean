/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExp.Basic


inductive Game_World.hist_on_turn_valid (g : Game_World α β) {t : Nat} : g.hist_on_turn_output t → Prop
| ofTerminal (result : {hist : List β // g.hist_legal hist ∧ hist.length = t}) : g.hist_on_turn_valid (.terminal result)
| ofNonterminal (result : {hist : List β // g.hist_legal hist ∧ hist.length = t}) (property : g.hist_neutral result.val) : g.hist_on_turn_valid (.nonterminal result property)


def Symm_Game_World.hist_on_turn_valid (g : Symm_Game_World α β) {t : Nat} (h : g.hist_on_turn_output t) : Prop :=
  Game_World.hist_on_turn_valid g.toGame_World h


lemma Game_World.hist_on_turn_valid_not_invalid (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  g.hist_on_turn fst_strat snd_strat t ≠ Game_World.hist_on_turn_output.invalid :=
  match Q : g.hist_on_turn fst_strat snd_strat t with
  | .invalid => by rw [Q] at V ; cases V
  | .terminal _ => Game_World.hist_on_turn_output.noConfusion
  | .nonterminal _ _ => Game_World.hist_on_turn_output.noConfusion


lemma Game.hist_on_turn_valid_not_invalid (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :
  g.hist_on_turn t ≠ Game_World.hist_on_turn_output.invalid :=
  Game_World.hist_on_turn_valid_not_invalid _ _ _ _ V


lemma Symm_Game_World.hist_on_turn_valid_not_invalid (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  g.hist_on_turn fst_strat snd_strat t ≠ Game_World.hist_on_turn_output.invalid :=
  by convert @Game_World.hist_on_turn_valid_not_invalid _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) fst_strat snd_strat t (by apply V)

lemma Symm_Game.hist_on_turn_valid_not_invalid (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)):
  g.hist_on_turn t ≠ Game_World.hist_on_turn_output.invalid :=
  Symm_Game_World.hist_on_turn_valid_not_invalid _ _ _ _ V



def Game_World.hist_on_turn_value (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  List β :=
  match Q : g.hist_on_turn fst_strat snd_strat t with
  | .invalid => False.elim ((g.hist_on_turn_valid_not_invalid _ _ _ V) Q)
  | .terminal res => res.val
  | .nonterminal res _ => res.val

def Game.hist_on_turn_value (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :=
  g.toGame_World.hist_on_turn_value g.fst_strat g.snd_strat t V



def Symm_Game_World.hist_on_turn_value (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  List β :=
  by convert @Game_World.hist_on_turn_value _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) fst_strat snd_strat t (by apply V)

def Symm_Game.hist_on_turn_value (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :=
  g.toSymm_Game_World.hist_on_turn_value g.fst_strat g.snd_strat t V



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


lemma Game.hist_on_turn_value_length (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :
  (g.hist_on_turn_value t V).length = t :=
  g.toGame_World.hist_on_turn_value_length g.fst_strat g.snd_strat t V



lemma Symm_Game_World.hist_on_turn_value_length (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  (g.hist_on_turn_value fst_strat snd_strat t V).length = t :=
  by convert @Game_World.hist_on_turn_value_length _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) fst_strat snd_strat t (by apply V)


lemma Symm_Game.hist_on_turn_value_length (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :
  (g.hist_on_turn_value t V).length = t :=
  g.toSymm_Game_World.hist_on_turn_value_length g.fst_strat g.snd_strat t V



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


lemma Game.hist_on_turn_value_legal (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :
  g.hist_legal (g.hist_on_turn_value t V) :=
  g.toGame_World.hist_on_turn_value_legal g.fst_strat g.snd_strat t V


lemma Symm_Game_World.hist_on_turn_value_legal (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) :
  g.hist_legal (g.hist_on_turn_value fst_strat snd_strat t V) :=
  by convert @Game_World.hist_on_turn_value_legal _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) fst_strat snd_strat t (by apply V)


lemma Symm_Game.hist_on_turn_value_legal (g : Symm_Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) (V : g.hist_on_turn_valid (g.hist_on_turn t)) :
  g.hist_legal (g.hist_on_turn_value t V) :=
  g.toSymm_Game_World.hist_on_turn_value_legal g.fst_strat g.snd_strat t V



lemma Game_World.hist_on_turn_value_zero (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat 0)} :
  (g.hist_on_turn_value fst_strat snd_strat 0 V) = [] :=
  by
  dsimp [hist_on_turn_value, hist_on_turn]
  split
  · rename_i no
    split_ifs at no
  · rename_i no
    split_ifs at no
    replace no := hist_on_turn_output.terminal.inj no
    apply Subtype.val_inj.mpr no.symm
  · rename_i no
    split_ifs at no
    replace no := hist_on_turn_output.nonterminal.inj no
    apply Subtype.val_inj.mpr no.symm



lemma Game_World.hist_on_turn_valid_of_valid_succ (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy} {t : Nat}
  (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat (t+1))) :
  g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t) :=
  by
  cases' t with t
  · dsimp [hist_on_turn]
    split_ifs with N
    · exact Game_World.hist_on_turn_valid.ofNonterminal _ _
    · exact Game_World.hist_on_turn_valid.ofTerminal _
  · dsimp [hist_on_turn]
    split


#exit

lemma Game_World.hist_on_turn_value_succ_turn_fst (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy} {t : Nat}
  {V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat (t+1))}
  (T : Turn_fst (t+1)) :
  (g.hist_on_turn_value fst_strat snd_strat (t+1) V) =
  fst_strat :=
