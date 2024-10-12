/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.HistoryAPI

-- # Staging


def Game_World.fStrat_staged (g : Game_World α β)
  (f_strat : g.fStrategy) (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∀ t, (ht : t < hist.length) → (T : Turn_fst (t+1)) →
    f_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (g.hist_legal_rtake _ _ leg)
    = ⟨ hist.rget ⟨t,ht⟩ , (g.hist_legal_rtake_fst _ _ T ht leg)⟩


def Game_World.fStrat_wHist (g : Game_World α β) (hist : List β) (leg : g.hist_legal hist) :=
  { f_strat : g.fStrategy // g.fStrat_staged f_strat hist leg}


def Game_World.sStrat_staged (g : Game_World α β)
  (s_strat : g.sStrategy) (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∀ t, (ht : t < hist.length) → (T : Turn_snd (t+1)) →
    s_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (g.hist_legal_rtake _ _ leg)
    = ⟨ hist.rget ⟨t,ht⟩ , (g.hist_legal_rtake_snd _ _ T ht leg)⟩


def Game_World.sStrat_wHist (g : Game_World α β) (hist : List β) (leg : g.hist_legal hist) :=
  { s_strat : g.sStrategy // g.sStrat_staged s_strat hist leg}


def Game_World.is_fst_staged_win  (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∃ ws : g.fStrat_wHist hist leg, ∀ snd_s : g.sStrat_wHist hist leg,
  ({g with fst_strat := ws.val, snd_strat := snd_s.val} : Game α β).fst_win


def Game_World.is_snd_staged_win  (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∃ ws : g.sStrat_wHist hist leg, ∀ fst_s : g.fStrat_wHist hist leg,
  ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win

inductive Game_World.has_staged_WL (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) : Prop where
  | wf (h : g.is_fst_staged_win hist leg)
  | ws (h : g.is_snd_staged_win hist leg)

lemma Game_World.fStrat_staged_empty (g : Game_World α β) (f_strat : g.fStrategy) :
  g.fStrat_staged f_strat [] Game_World.hist_legal.nil := by
  intro _ no
  contradiction

lemma Game_World.sStrat_staged_empty (g : Game_World α β) (s_strat : g.sStrategy) :
  g.sStrat_staged s_strat [] Game_World.hist_legal.nil := by
  intro _ no
  contradiction

lemma Game_World.has_WL_iff_has_staged_WL_empty (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] :
  g.has_WL ↔ g.has_staged_WL [] Game_World.hist_legal.nil :=
  by
  constructor
  · intro h
    cases' h with h h
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_staged_WL.wf
      use ⟨ws, g.fStrat_staged_empty ws⟩
      intro s_strat
      exact ws_prop s_strat.val
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_staged_WL.ws
      use ⟨ws, g.sStrat_staged_empty ws⟩
      intro s_strat
      exact ws_prop s_strat.val
  · intro h
    cases' h with h h
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_WL.wf
      use ws.val
      intro s_strat
      exact ws_prop ⟨s_strat, g.sStrat_staged_empty s_strat⟩
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_WL.ws
      use ws.val
      intro s_strat
      exact ws_prop ⟨s_strat, g.fStrat_staged_empty s_strat⟩
