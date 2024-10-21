
/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Basic


inductive Game_World.Turn_isWL (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop where
| wf : g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn
| ws : g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.Turn_isWL (g : Symm_Game_World α β)
  (f_strat : fStrategy g.init_game_state g.law g.law)
  (s_strat : sStrategy g.init_game_state g.law g.law) (turn : ℕ) : Prop :=
  --g.win_states (g.state_on_turn f_strat s_strat turn)
  Game_World.Turn_isWL (g.toGame_World) f_strat s_strat turn


def Game_World.isWL (g : Game_World α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∃ turn, g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.isWL (g : Symm_Game_World α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.law g.law),
  ∀ (s_strat : sStrategy g.init_game_state g.law g.law),
  ∃ turn, g.Turn_isWL f_strat s_strat turn

def Game_World.isWL_wBound (g : Game_World α β) (T : ℕ): Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∃ turn ≤ T, g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.isWL_wBound (g : Symm_Game_World α β) (T : ℕ): Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.law g.law),
  ∀ (s_strat : sStrategy g.init_game_state g.law g.law),
  ∃ turn ≤ T, g.Turn_isWL f_strat s_strat turn



def Game_World.state_on_turn_neutral (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop :=
  ¬ g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.state_on_turn_neutral (g : Symm_Game_World α β)
  (f_strat : fStrategy g.init_game_state g.law g.law)
  (s_strat : sStrategy g.init_game_state g.law g.law) (turn : ℕ) : Prop :=
  Game_World.state_on_turn_neutral (g.toGame_World) f_strat s_strat turn

def Game.state_on_turn_neutral (g : Game α β) (turn : ℕ) : Prop :=
  g.toGame_World.state_on_turn_neutral g.fst_strat g.snd_strat turn

def Symm_Game.state_on_turn_neutral (g : Symm_Game α β) (turn : ℕ) : Prop :=
  g.toGame.state_on_turn_neutral turn


def Game.fst_win  {α β : Type _} (g : Game α β) : Prop :=
  ∃ turn : ℕ, g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game.snd_win  {α β : Type _} (g : Game α β) : Prop :=
  ∃ turn : ℕ, g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Symm_Game.fst_win  {α β : Type _} (g : Symm_Game α β) : Prop :=
  g.toGame.fst_win

def Symm_Game.snd_win  {α β : Type _} (g : Symm_Game α β) : Prop :=
  g.toGame.snd_win

def Game_World.is_fst_win  {α β : Type _} (g : Game_World α β) : Prop :=
  ∃ ws : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ snd_s : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game α β).fst_win

def Game_World.is_snd_win  {α β : Type _} (g : Game_World α β) : Prop :=
  ∃ ws : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ fst_s : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := fst_s, snd_strat := ws} : Game α β).snd_win

def Symm_Game_World.is_fst_win  {α β : Type _} (g : Symm_Game_World α β) : Prop :=
  g.toGame_World.is_fst_win

def Symm_Game_World.is_snd_win  {α β : Type _} (g : Symm_Game_World α β) : Prop :=
  g.toGame_World.is_snd_win

inductive Game_World.has_WL (g : Game_World α β) : Prop where
| wf (h : g.is_fst_win)
| ws (h : g.is_snd_win)

def Symm_Game_World.has_WL (g : Symm_Game_World α β) := g.toGame_World.has_WL


def State_from_history_neutral (ini : α ) (f_wins s_wins : α → List β → Prop) (hist : List β) : Prop :=
  (¬ (f_wins ini hist)) ∧ (¬ (s_wins ini hist))


lemma Game_World.state_on_turn_neutral_State_from_history_neutral (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) :
  g.state_on_turn_neutral f_strat s_strat turn ↔
  State_from_history_neutral g.init_game_state g.fst_win_states g.snd_win_states
  (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn).val :=
  by
  dsimp [Game_World.state_on_turn_neutral, State_from_history_neutral]
  rw [← not_or, not_iff_not]
  constructor
  · intro h
    cases' h with F S
    · left ; exact F
    · right ; exact S
  · intro h
    cases' h with F S
    · apply Game_World.Turn_isWL.wf ; exact F
    · apply Game_World.Turn_isWL.ws ; exact S




-- # Coherent end

structure Game_World.coherent_end (g : Game_World α β) : Prop where
  em : ∀ hist, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → ¬ (g.fst_win_states g.init_game_state hist ∧ g.snd_win_states g.init_game_state hist)
  fst : ∀ hist, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → (g.fst_win_states g.init_game_state hist →
          ∀ act, ((Turn_fst (hist.length+1) → g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (hist.length+1) → g.snd_legal g.init_game_state hist act)) →
            g.fst_win_states g.init_game_state (act :: hist))
  snd : ∀ hist, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → (g.snd_win_states g.init_game_state hist →
          ∀ act, ((Turn_fst (hist.length+1) → g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (hist.length+1) → g.snd_legal g.init_game_state hist act)) →
            g.snd_win_states g.init_game_state (act :: hist))




lemma Game_World.coherent_end_all_fst (g : Game_World α β)  (h : g.coherent_end)
  (hist : List β) (hw : g.fst_win_states g.init_game_state hist)
  (future : List β) (fleg : Hist_legal g.init_game_state g.fst_legal g.snd_legal (future ++ hist)) :
  g.fst_win_states g.init_game_state (future ++ hist) :=
  by
  induction' future with x l ih
  · apply hw
  · cases' fleg
    rename_i sofar now
    rw [List.cons_append]
    apply h.fst _ sofar (ih sofar)
    constructor
    · intro T
      rw [if_pos T] at now
      exact now
    · intro T
      rw [Turn_snd_iff_not_fst] at T
      rw [if_neg T] at now
      exact now


lemma Game_World.coherent_end_all_snd (g : Game_World α β)  (h : g.coherent_end)
  (hist : List β) (hw : g.snd_win_states g.init_game_state hist)
  (future : List β) (fleg : Hist_legal g.init_game_state g.fst_legal g.snd_legal (future ++ hist)) :
  g.snd_win_states g.init_game_state (future ++ hist) :=
  by
  induction' future with x l ih
  · apply hw
  · cases' fleg
    rename_i sofar now
    rw [List.cons_append]
    apply h.snd _ sofar (ih sofar)
    constructor
    · intro T
      rw [if_pos T] at now
      exact now
    · intro T
      rw [Turn_snd_iff_not_fst] at T
      rw [if_neg T] at now
      exact now


lemma Game_World.coherent_end_for_starts (g : Game_World α β) (hg : g.coherent_end) :
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (t : ℕ),
    (g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t) → g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat (t+1))) ∧
      (g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t) → g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat (t+1))) :=
  by
  intro f_strat s_strat t
  constructor
  · intro fw
    dsimp [History_on_turn]
    split_ifs with T
    · apply hg.fst _ (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1
      · exact fw
      · constructor
        · intro T'
          apply (f_strat (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).val T' (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1).prop
        · intro no
          rw [(History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.2, Turn_snd_iff_not_fst] at no
          exfalso
          exact no T
    · apply hg.fst _ (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1
      · exact fw
      · constructor
        · intro no
          rw [(History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.2, Turn_fst_iff_not_snd] at no
          exfalso
          exact no T
        · intro T'
          apply (s_strat (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).val T' (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1).prop
  · intro fw
    dsimp [History_on_turn]
    split_ifs with T
    · apply hg.snd _ (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1
      · exact fw
      · constructor
        · intro T'
          apply (f_strat (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).val T' (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1).prop
        · intro no
          rw [(History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.2, Turn_snd_iff_not_fst] at no
          exfalso
          exact no T
    · apply hg.snd _ (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1
      · exact fw
      · constructor
        · intro no
          rw [(History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.2, Turn_fst_iff_not_snd] at no
          exfalso
          exact no T
        · intro T'
          apply (s_strat (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).val T' (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).prop.1).prop

lemma Game_World.coherent_end_all_for_strats (g : Game_World α β)  (h : g.coherent_end)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (t n : ℕ) :
  (g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t) → g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat (t+n))) ∧
    (g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t) → g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat (t+n))) :=
  by
  replace h := g.coherent_end_for_starts h
  constructor
  · intro H
    induction' n with n ih
    · dsimp
      exact H
    · apply (h f_strat s_strat (t+n)).1
      exact ih
  · intro H
    induction' n with n ih
    · dsimp
      exact H
    · apply (h f_strat s_strat (t+n)).2
      exact ih



lemma Game.coherent_end_fst_win (g : Game α β) (hg : g.coherent_end)
  (main : ∃ turn : ℕ, g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn)) :
  g.fst_win :=
  by
  obtain ⟨t,fw⟩ := main
  let S : Set Nat := {n : Nat | g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat n)}
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
      apply hg.em _ (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat m).prop.1 ⟨(mdef),con⟩



lemma Game.coherent_end_snd_win (g : Game α β) (hg : g.coherent_end)
  (main : ∃ turn : ℕ, g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn)) :
  g.snd_win :=
  by
  obtain ⟨t,fw⟩ := main
  let S : Set Nat := {n : Nat | g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat n)}
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
      apply hg.em _ (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat m).prop.1 ⟨con,mdef⟩
    · apply mm n con nlm


def Symm_Game_World.coherent_end (g : Symm_Game_World α β) : Prop := g.toGame_World.coherent_end



-- # With draw states



inductive Game_World_wDraw.Turn_isWLD (g : Game_World_wDraw α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop where
| wf : g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| ws : g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| drw : g.draw_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn


def Game_World_wDraw.isWLD (g : Game_World_wDraw α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∃ turn, g.Turn_isWLD f_strat s_strat turn


def Game_World_wDraw.state_on_turn_neutral (g : Game_World_wDraw α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop :=
  ¬ g.Turn_isWLD f_strat s_strat turn


def Game_wDraw.state_on_turn_neutral (g : Game_wDraw α β) (turn : ℕ) : Prop :=
  g.toGame_World_wDraw.state_on_turn_neutral g.fst_strat g.snd_strat turn


def Game_wDraw.fst_win  {α β : Type _} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, g.fst_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game_wDraw.snd_win  {α β : Type _} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, g.snd_win_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game_wDraw.draw  {α β : Type _} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, g.draw_states g.init_game_state (History_on_turn g.init_game_state g.fst_legal g.snd_legal g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game_World_wDraw.is_fst_win  {α β : Type _} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ snd_s : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw α β).fst_win

def Game_World_wDraw.is_snd_win  {α β : Type _} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ fst_s : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := fst_s, snd_strat := ws} : Game_wDraw α β).snd_win

def Game_World_wDraw.is_draw_fst {α β : Type _} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ snd_s : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw  α β).draw

def Game_World_wDraw.is_draw_snd {α β : Type _} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ fst_s : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := fst_s, snd_strat := ws} : Game_wDraw  α β).draw

def Game_World_wDraw.is_draw {α β : Type _} (g : Game_World_wDraw α β) : Prop := g.is_draw_fst ∨ g.is_draw_snd


inductive Game_World_wDraw.has_WLD (g : Game_World_wDraw α β) : Prop where
| wf (h : g.is_fst_win)
| ws (h : g.is_snd_win)
| draw (h : g.is_draw)

def State_from_history_neutral_wDraw (ini : α ) (f_wins s_wins draw : α → List β → Prop) (hist : List β) : Prop :=
  (¬ (f_wins ini hist)) ∧ (¬ (s_wins ini hist) ∧ (¬ (draw ini hist)))


lemma Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral (g : Game_World_wDraw α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) :
  g.state_on_turn_neutral f_strat s_strat turn ↔
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states
  (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn).val :=
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



def Game_World_wDraw.is_draw_at_worst_fst {α β : Type _} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ snd_s : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw α β).fst_win ∨
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw  α β).draw

def Game_World_wDraw.is_draw_at_worst_snd {α β : Type _} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ fst_s : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := fst_s, snd_strat := ws} : Game_wDraw α β).snd_win ∨
  ({g with fst_strat := fst_s, snd_strat := ws} : Game_wDraw  α β).draw
