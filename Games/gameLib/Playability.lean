/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.HistoryAPI


/-
This file defines a property of game worlds we call "playability".
It is required by Zermelo's theorem, for example.

Its definition is `Game_World.playable`, and the rest of the file
contains API surrounding this notion.
-/

/--
A `Game_World` is playable if, given a legal history of moves,
there exists a legal move to be played at this stage, for either
player.
-/
def Game_World.playable (g : Game_World α β) : Prop :=
  ∀ hist : List β, g.hist_legal hist →
    ((Turn_fst (List.length hist + 1) → ∃ act : β, g.fst_legal hist act) ∧ (Turn_snd (List.length hist + 1) → ∃ act : β, g.snd_legal hist act))

def Symm_Game_World.playable (g : Symm_Game_World α β) : Prop := g.toGame_World.playable


noncomputable
def Game_World.exStrat_fst (g : Game_World α β) (hg : g.playable) : g.fStrategy :=
  fun hist T leg  => Classical.choice <| let ⟨x, xp⟩ := ((hg hist leg).1 T); ⟨(⟨x, xp⟩ : { act // g.fst_legal hist act })⟩

noncomputable
def Game_World.exStrat_snd (g : Game_World α β) (hg : g.playable) : g.sStrategy :=
  fun hist T leg => Classical.choice <| let ⟨x, xp⟩ := ((hg hist leg).2 T); ⟨(⟨x, xp⟩ : { act // g.snd_legal hist act })⟩

lemma Game_World.exStrat_Hist_legal (g : Game_World α β) (hg : g.playable):
  ∀ t, g.hist_legal (g.hist_on_turn (g.exStrat_fst hg) (g.exStrat_snd hg) t) :=
  by
  apply Game_World.hist_on_turn_legal


def Game_World.cPlayable_fst (g : Game_World α β) : Type _ :=
  (hist : List β) → (pl : g.hist_legal hist) → (Turn_fst (List.length hist + 1)) → {act : β // g.fst_legal hist act}

def Game_World.cPlayable_snd (g : Game_World α β) : Type _ :=
  (hist : List β) → (pl : g.hist_legal hist) → (Turn_snd (List.length hist + 1)) → {act : β // g.snd_legal hist act}
