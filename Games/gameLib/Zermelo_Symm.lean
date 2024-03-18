/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Mathlib.Tactic

/-
Note to self:

Try easier Zermelo with a symmetric win-loose game
-/

inductive Symm_Game_World.has_WL (g : Symm_Game_World α β) : Prop where
| wf : g.is_fst_win → g.has_WL
| ws : g.is_snd_win → g.has_WL


def Symm_Game_World.world_after_fst {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : Symm_Game_World α β := -- act not required to be legal
  {g with init_game_state := g.transition [] fst_act }
  -- maybe swap fst and snd notions ? Cause we expect snd player to go fst now



@[simp]
lemma Symm_Game_World.world_after_fst_init {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.transition [] fst_act :=
  by rfl

@[simp]
lemma Symm_Game_World.world_after_fst_law {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).law = g.law :=
  by rfl

@[simp]
lemma Symm_Game_World.world_after_fst_win_states {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).win_states = g.win_states :=
  by rfl


@[simp]
lemma Symm_Game_World.world_after_fst_snd_win_states {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).win_states = g.win_states :=
  by rfl



instance (l : List α): Decidable (l = []) :=
  by
  match l with
  | [] => apply isTrue ; rfl
  | x :: L => apply isFalse ; exact List.cons_ne_nil x L


lemma Symm_Game_World.History_of_preconditioned'
  (g: Symm_Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  History_on_turn g.init_game_state fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) ++ [fst_act] :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [History_on_turn, Turn_fst]
    rw [if_pos (by decide), if_pos (by rfl)]
  · dsimp only [History_on_turn] at *
    by_cases q : Turn_fst (t+1)
    · rw [Turn_fst_not_step] at q
      rw [if_neg q] at *
      rw [← Turn_fst_not_step] at q
      rw [if_pos q, if_pos q] at *
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Symm_Game_World.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]
    · rw [if_neg q, if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q] at *
      rw [if_neg (by apply List.cons_ne_nil)]
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Symm_Game_World.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]

-- TDOD: rephrase ↓ with ↑

def Symm_Game_World.law_blind_fst' (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.law (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    ↔ g.law (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Symm_Game_World.law_blind_snd' (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.law (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    ↔ g.law (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Symm_Game_World.law_blind' (g : Symm_Game_World α β) : Prop :=
 g.law_blind_fst' ∧ g.law_blind_snd'


def Symm_Game_World.transition_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.transition (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.transition (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Symm_Game_World.transition_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.transition (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.transition (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Symm_Game_World.transition_blind (g : Symm_Game_World α β) : Prop :=
 g.transition_blind_fst ∧ g.transition_blind_snd

lemma Symm_Game_World.State_of_preconditioned
  (g: Symm_Game_World α β)
  (tb : g.transition_blind)
  (fst_act: β)
  (fst_act_legal: g.law [] fst_act)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  g.state_on_turn fst_strat snd_strat (turn + 1) =
  (g.world_after_fst fst_act).state_on_turn f_strat s_strat turn :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [state_on_turn]
    rw [if_pos (by decide)]
    dsimp [history_on_turn, History_on_turn]
    rw [if_pos (by rfl)]
  · dsimp [state_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q]
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      dsimp [history_on_turn]
      have := g.History_of_preconditioned' fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.2 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (f_strat (transition g [] fst_act) (History_on_turn (transition g [] fst_act) f_strat s_strat t))
      rw [← this]
      clear this
      rfl
    · rw [Turn_not_fst_iff_snd, Turn_snd_fst_step] at q
      rw [if_pos q]
      dsimp [history_on_turn]
      rw [← Turn_fst_step, Turn_fst_not_step] at q
      rw [if_neg q]
      rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
      have := g.History_of_preconditioned' fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.1 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (s_strat (transition g [] fst_act) (History_on_turn (transition g [] fst_act) f_strat s_strat t))
      rw [← this]
      clear this
      rfl


lemma Symm_Game_World.fst_legal_preconditioned'
  (g: Symm_Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.law [] fst_act)
  (f_strat s_strat : Strategy α β)
  (s_leg: Strategy_legal_snd (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).law) f_strat s_strat)
  (b : g.law_blind_fst')
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal_fst g.init_game_state (fun x => g.law) fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · dsimp [History_on_turn]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · rw [← b, Symm_Game_World.History_of_preconditioned']
    · dsimp [History_on_turn]
      rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil fst_act [])]
      rw [List.dropLast_concat]
      apply s_leg
      rw [Turn_snd_fst_step]
      exact tf
    · exact fst_act_legal


lemma Symm_Game_World.snd_legal_preconditioned'
  (g: Symm_Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.law [] fst_act)
  (f_strat s_strat : Strategy α β)
  (f_leg: Strategy_legal_fst (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).law) f_strat s_strat)
  (b : g.law_blind_snd')
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal_snd g.init_game_state (fun x => g.law) fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · contradiction
  · rw [← b, Symm_Game_World.History_of_preconditioned']
    · dsimp [History_on_turn]
      rw [List.dropLast_concat]
      apply f_leg
      rw [Turn_fst_snd_step]
      exact tf
    · exact fst_act_legal


inductive Symm_Game_World.Turn_isWL (g : Symm_Game_World α β) (f_strat s_strat : Strategy α β) (turn : ℕ) : Prop where
| wf : Turn_fst turn → g.win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn
| ws : Turn_snd turn → g.win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.isWL_wBound (g : Symm_Game_World α β) (T : ℕ) : Prop :=
    ∀ f_strat s_strat : Strategy α β,
    (f_leg : Strategy_legal_fst g.init_game_state (fun _ => g.law) f_strat s_strat) →
    (s_leg : Strategy_legal_snd g.init_game_state (fun _ => g.law) f_strat s_strat) →
    ∃ turn ≤ T, g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.nontrivial (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat : Strategy α β, ¬ (g.Turn_isWL f_strat s_strat 0)

def Symm_Game_World.playable (g : Symm_Game_World α β) : Prop :=
  ∃ f_strat s_strat : Strategy α β,
  (Strategy_legal_fst g.init_game_state (fun _ => g.law) f_strat s_strat) ∧
  (Strategy_legal_snd g.init_game_state (fun _ => g.law) f_strat s_strat)

structure Symm_Game_World_Z (α β : Type u) extends Symm_Game_World α β where
  lb : toSymm_Game_World.law_blind'
  nt : toSymm_Game_World.nontrivial
  tb : toSymm_Game_World.transition_blind
  p : toSymm_Game_World.playable


lemma Symm_Game_World_Z.conditioning_bound
  (g : Symm_Game_World_Z α β)
  {T : ℕ} (hg : g.isWL_wBound (T + 1))
  (fst_act : β) (leg : g.law [] fst_act):
  (g.world_after_fst fst_act).isWL_wBound T :=
  by
  intro f_strat s_strat f_leg s_leg
  let fst_strat : Strategy α β := fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)
  let snd_strat : Strategy α β := fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)
  specialize hg fst_strat snd_strat _ _
  · apply g.fst_legal_preconditioned' fst_act leg  f_strat s_strat s_leg g.lb.1
  · apply g.snd_legal_preconditioned' fst_act leg  f_strat s_strat f_leg g.lb.2
  · obtain ⟨t, t_bd, t_prop⟩ := hg
    cases' t with t
    · exfalso
      exact (g.nt fst_strat snd_strat) t_prop
    · rw [Nat.succ_le_succ_iff] at t_bd
      use t
      constructor
      · exact t_bd
      · cases' t_prop with tp c tp c c
        · apply Symm_Game_World.Turn_isWL.ws
          · rw [Turn_snd_fst_step] ; exact tp
          · rw [← Symm_Game_World.State_of_preconditioned]
            · rw [Symm_Game_World.world_after_fst_snd_win_states]
              exact c
            · exact g.tb
            · exact leg
        · apply Symm_Game_World.Turn_isWL.wf
          · rw [Turn_fst_snd_step] ; exact tp
          · rw [← Symm_Game_World.State_of_preconditioned]
            · rw [Symm_Game_World.world_after_fst_win_states]
              exact c
            · exact g.tb
            · exact leg

lemma Symm_Game_World.conditioning_WLD_helper
  (g : Symm_Game_World α β)
  (hwld : g.has_WL)
  (hnfw : ¬ g.is_fst_win):
  g.is_snd_win :=
  by
  cases' hwld -- <;> { contradiction <|> assumption } --fails...
  · contradiction
  · assumption


open Classical

lemma Symm_Game_World_Z.conditioning_WLD
  [Inhabited β]
  (g : Symm_Game_World_Z α β)
  (h : ∀ fst_act : β, g.law [] fst_act → (g.world_after_fst fst_act).has_WL) :
  g.has_WL :=
  by
  by_cases qwf : ∃ f_act : β, g.law [] f_act ∧ (g.world_after_fst f_act).is_fst_win
  · sorry
  · push_neg at qwf
    apply Symm_Game_World.has_WL.ws
    let ws := fun (ini : α) hist  => if hh : hist = [] -- shouldn't happen, as snd strat
                              then default -- dummy
                              else let f_act := List.getLast hist hh
                                   if H : g.law [] f_act -- should be the cases ?!?
                                   then (Classical.choose ((g.world_after_fst f_act).conditioning_WLD_helper
                                                            (h f_act H)
                                                            (qwf f_act H)))
                                          ini hist -- is it ?
                                   else default
    use ws
    intro f_strat ws_leg f_leg
    let f_act := f_strat g.init_game_state []
    sorry


lemma Symm_Game_World_Z.Zermelo
  [Inhabited β]
  (g : Symm_Game_World_Z α β)
  {T : ℕ} (hg : g.isWL_wBound T)
  : g.has_WL :=
  by
  revert g
  induction' T with t ih
  · intro g t0
    dsimp [Symm_Game_World.isWL_wBound] at t0
    obtain ⟨f_strat, s_strat, f_leg, s_leg⟩ := g.p
    obtain ⟨t, tl0, t_end⟩ := t0 f_strat s_strat f_leg s_leg
    rw [Nat.le_zero] at tl0
    rw [tl0] at t_end
    cases' t_end
    · rename_i tt ttt; contradiction
    · apply Symm_Game_World.has_WL.ws
      use (fun _ _ => default)
      intro f_strat' leg f_leg'
      use 0
      constructor
      · decide
      · constructor
        · dsimp [Game.state_on_turn]
          rename_i h ; exact h
        · intro t ahhh ; contradiction
  · intro g bd
    apply Symm_Game_World_Z.conditioning_WLD
    intro f_act f_leg
    apply ih ((Symm_Game_World.world_after_fst g.toSymm_Game_World f_act))
    · exact Game_World_wDraw.conditioning_bound g bd f_act f_leg hp.bl hp.nt hp.tb hp.wb
    · exact pl
