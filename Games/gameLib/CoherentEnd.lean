/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination

/-
This file defines a property of game worlds we call "coherent end".
It is required by Zermelo's theorem, for example.

It's definition is `Game_World.coherent_end`, and the rest of the file
contains API surrounding this notion.
-/


/--
A `Game_World` has a coherent end if:
- `em` : the predicates deciding the winning condition for each player
  can't both be satisfied at the same time.
- `fst` and `snd` : if the game has reached a winning state, then no matter
  the moves played after, the game will stay in that winnning state for the
  respective player.
-/
structure Game_World.coherent_end (g : Game_World α β) : Prop where
  em : ∀ hist, g.hist_legal hist → ¬ (g.fst_win_states hist ∧ g.snd_win_states hist)
  fst : ∀ hist, g.hist_legal hist → (g.fst_win_states hist →
          ∀ act, ((Turn_fst (hist.length+1) → g.fst_legal hist act) ∧ (Turn_snd (hist.length+1) → g.snd_legal hist act)) →
            g.fst_win_states (act :: hist))
  snd : ∀ hist, g.hist_legal hist → (g.snd_win_states hist →
          ∀ act, ((Turn_fst (hist.length+1) → g.fst_legal hist act) ∧ (Turn_snd (hist.length+1) → g.snd_legal hist act)) →
            g.snd_win_states (act :: hist))


def Symm_Game_World.coherent_end (g : Symm_Game_World α β) : Prop := g.toGame_World.coherent_end


lemma Game_World.coherent_end_all_fst (g : Game_World α β)  (h : g.coherent_end)
  (hist : List β) (hw : g.fst_win_states hist)
  (future : List β) (fleg : g.hist_legal (future ++ hist)) :
  g.fst_win_states (future ++ hist) :=
  by
  induction' future with x l ih
  · apply hw
  · cases' fleg ; rename_i sofar now ;rw [List.cons_append] ; apply h.fst _ sofar (ih sofar)
    constructor
    · intro T ; rw [if_pos T] at now ; exact now
    · intro T ; rw [Turn_snd_iff_not_fst] at T ; rw [if_neg T] at now ; exact now

lemma Game_World.coherent_end_all_snd (g : Game_World α β)  (h : g.coherent_end)
  (hist : List β) (hw : g.snd_win_states hist)
  (future : List β) (fleg : g.hist_legal (future ++ hist)) :
  g.snd_win_states (future ++ hist) :=
  by
  induction' future with x l ih
  · apply hw
  · cases' fleg ; rename_i sofar now ; rw [List.cons_append] ; apply h.snd _ sofar (ih sofar)
    constructor
    · intro T ; rw [if_pos T] at now ;exact now
    · intro T ; rw [Turn_snd_iff_not_fst] at T ; rw [if_neg T] at now ; exact now

lemma Game_World.coherent_end_for_starts (g : Game_World α β)
  (hg : g.coherent_end) (f_strat : g.fStrategy) (s_strat : g.sStrategy) (t : ℕ) :
    (g.fst_win_states (g.hist_on_turn f_strat s_strat t) → g.fst_win_states (g.hist_on_turn f_strat s_strat (t+1))) ∧
      (g.snd_win_states (g.hist_on_turn f_strat s_strat t) → g.snd_win_states (g.hist_on_turn f_strat s_strat (t+1))) :=
  by
  let H := g.hist_on_turn f_strat s_strat t
  dsimp [hist_on_turn]
  constructor
  · intro fw
    split_ifs with T
    · apply hg.fst _ H.prop.1 fw
      constructor
      · intro T' ; apply (f_strat H.val T' H.prop.1).prop
      · intro no ; rw [H.prop.2, Turn_snd_iff_not_fst] at no ; exfalso ; exact no T
    · apply hg.fst _ H.prop.1 fw
      constructor
      · intro no ; rw [H.prop.2, Turn_fst_iff_not_snd] at no ; exfalso ; exact no T
      · intro T' ; apply (s_strat H.val T' H.prop.1).prop
  · intro fw
    split_ifs with T
    · apply hg.snd _ H.prop.1 fw
      constructor
      · intro T' ; apply (f_strat H.val T' H.prop.1).prop
      · intro no ; rw [H.prop.2, Turn_snd_iff_not_fst] at no ; exfalso ; exact no T
    · apply hg.snd _ H.prop.1 fw
      constructor
      · intro no ; rw [H.prop.2, Turn_fst_iff_not_snd] at no ; exfalso ; exact no T
      · intro T' ; apply (s_strat H.val T' H.prop.1).prop


lemma Game_World.coherent_end_all_for_strats (g : Game_World α β)  (h : g.coherent_end)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (t n : ℕ) :
  (g.fst_win_states (g.hist_on_turn f_strat s_strat t) → g.fst_win_states (g.hist_on_turn f_strat s_strat (t+n))) ∧
      (g.snd_win_states (g.hist_on_turn f_strat s_strat t) → g.snd_win_states (g.hist_on_turn f_strat s_strat (t+n))) :=
  by
  replace h := g.coherent_end_for_starts h
  constructor
  · intro H
    induction' n with n ih
    · exact H
    · exact (h f_strat s_strat (t+n)).1 ih
  · intro H
    induction' n with n ih
    · exact H
    · exact (h f_strat s_strat (t+n)).2 ih


lemma Game.coherent_end_fst_win (g : Game α β) (hg : g.coherent_end)
  (main : ∃ turn : ℕ, g.fst_win_states (g.hist_on_turn turn)) :
  g.fst_win :=
  by
  obtain ⟨t,fw⟩ := main
  let S : Set Nat := {n : Nat | g.fst_win_states (g.hist_on_turn n)}
  obtain ⟨m,mdef,mm⟩ := WellFounded.wellFounded_iff_has_min.mp Nat.lt_wfRel.wf S (by use t ; apply fw)
  use m
  constructor
  · apply mdef
  · intro n nlm
    unfold state_on_turn_neutral Game_World.state_on_turn_neutral
    by_contra con
    cases' con with con con
    · apply mm n con nlm
    · replace con := (g.coherent_end_all_for_strats hg g.fst_strat g.snd_strat n (m - n)).2 con
      rw [← Nat.add_sub_assoc (le_of_lt nlm), Nat.add_sub_self_left] at con
      apply hg.em _ (g.hist_on_turn m).prop.1 ⟨(mdef),con⟩

lemma Game.coherent_end_snd_win (g : Game α β) (hg : g.coherent_end)
  (main : ∃ turn : ℕ, g.snd_win_states (g.hist_on_turn turn)) :
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
