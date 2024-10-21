/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExp.Termination


def Game_World.coherent_end (g : Game_World α β) [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  ∀ (fst_strat : g.fStrategy ), ∀ (snd_strat : g.sStrategy),
  ∀ (t : ℕ), (V : g.hist_on_turn_valid (g.hist_on_turn fst_strat snd_strat t)) →
    ¬ (g.fst_win_states (g.hist_on_turn_value fst_strat snd_strat t V) ∧ g.snd_win_states (g.hist_on_turn_value fst_strat snd_strat t V))

def Symm_Game_World.coherent_end (g : Symm_Game_World α β) [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] : Prop :=
  @Game_World.coherent_end _ _ g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win])

lemma Game.coherent_end_fst_win (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.coherent_end) (main : ∃ turn : ℕ, ∃ (V : g.Turn_isWL g.fst_strat g.snd_strat turn),
    g.fst_win_states (g.hist_on_turn_value turn (g.hist_valid_of_turn_isWL V))) :
  g.fst_win :=
  by
  obtain ⟨t,tn,fw⟩ := main
  let S : Set Nat := {n : Nat | ∃ (V : g.Turn_isWL g.fst_strat g.snd_strat n), g.fst_win_states (g.hist_on_turn_value n (g.hist_valid_of_turn_isWL V))}
  obtain ⟨m,⟨m_N,m_W⟩ ,mm⟩ := WellFounded.wellFounded_iff_has_min.mp Nat.lt_wfRel.wf S (by use t ; use tn)
  use m
  use m_N
  constructor
  · apply m_W
  · intro n nlm
    unfold state_on_turn_neutral Game_World.state_on_turn_neutral
    by_contra con
    apply mm n (by use  con ; apply m_W)
    --obtain ⟨res,resdef⟩ := con
    -- cases' con with con con
    -- · apply mm n con nlm
    -- · replace con := (g.coherent_end_all_for_strats hg g.fst_strat g.snd_strat n (m - n)).2 con
    --   rw [← Nat.add_sub_assoc (le_of_lt nlm), Nat.add_sub_self_left] at con
    --   apply hg.em _ (g.hist_on_turn m).prop.1 ⟨(mdef),con⟩

lemma Game.coherent_end_snd_win (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.coherent_end) (main : ∃ turn : ℕ, g.snd_win_states (g.hist_on_turn turn)) :
  g.snd_win :=
  by
  obtain ⟨t,fw⟩ := main
  let S : Set Nat := {n : Nat | g.snd_win_states (g.hist_on_turn n)}
  obtain ⟨m,mdef,mm⟩ := WellFounded.wellFounded_iff_has_min.mp Nat.lt_wfRel.wf S (by use t ; apply fw)
  use m
  constructor
  · apply mdef
  · intro n nlm
    unfold state_on_turn_neutral Game_World.state_on_turn_neutral
    by_contra con
    cases' con with con con
    · replace con := (g.coherent_end_all_for_strats hg g.fst_strat g.snd_strat n (m - n)).1 con
      rw [← Nat.add_sub_assoc (le_of_lt nlm), Nat.add_sub_self_left] at con
      apply hg.em _ (g.hist_on_turn m).prop.1 ⟨con,mdef⟩
    · apply mm n con nlm
