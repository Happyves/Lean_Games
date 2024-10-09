/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExp.HistoryAPI


def Game_World.playable (g : Game_World α β) : Prop :=
  ∀ hist : List β, g.hist_legal hist → g.hist_neutral hist →
    ((Turn_fst (List.length hist + 1) → ∃ act : β, g.fst_legal hist act) ∧ (Turn_snd (List.length hist + 1) → ∃ act : β, g.snd_legal hist act))


noncomputable
def Game_World.exStrat_fst (g : Game_World α β) (hg : g.playable) : g.fStrategy :=
  fun hist T leg N => Classical.choice <| let ⟨x, xp⟩ := ((hg hist leg N).1 T); ⟨(⟨x, xp⟩ : { act // g.fst_legal hist act })⟩

noncomputable
def Game_World.exStrat_snd (g : Game_World α β) (hg : g.playable) : g.sStrategy :=
  fun hist T leg N => Classical.choice <| let ⟨x, xp⟩ := ((hg hist leg N).2 T); ⟨(⟨x, xp⟩ : { act // g.snd_legal hist act })⟩


lemma Game_World.exStrat_Hist_legal (g : Game_World α β) (hg : g.playable)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] :
  ∀ t, (V : g.hist_on_turn_valid (g.hist_on_turn (g.exStrat_fst hg) (g.exStrat_snd hg) t)) →
  g.hist_legal (g.hist_on_turn_value (g.exStrat_fst hg) (g.exStrat_snd hg) t V) :=
  by
  apply Game_World.hist_on_turn_value_legal
