/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Games.gameLib.Termination





def Game_World_wDraw.world_after_fst {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : Game_World_wDraw α β := -- act not required to be legal
  {g with init_game_state := g.fst_transition g.init_game_state [] fst_act }


@[simp]
lemma Game_World_wDraw.world_after_fst_init {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.fst_transition g.init_game_state [] fst_act :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_fst_legal {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_legal = g.fst_legal :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_snd_legal {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_legal = g.snd_legal :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_fst_win_states {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_win_states = g.fst_win_states :=
  by rfl


@[simp]
lemma Game_World_wDraw.world_after_fst_snd_win_states {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_win_states = g.snd_win_states :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_draw_states {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).draw_states = g.draw_states :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_fst_transition {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_transition = g.fst_transition :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_snd_transition {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_transition = g.snd_transition :=
  by rfl



-- # Coherent end

structure Game_World_wDraw.coherent_end_aux
  (g : Game_World_wDraw α β) (f_strat s_strat : Strategy α β) (t : ℕ) : Prop where
  f : g.fst_win_states (g.state_on_turn f_strat s_strat t) → g.fst_win_states (g.state_on_turn f_strat s_strat (t+1))
  s : g.snd_win_states (g.state_on_turn f_strat s_strat t) → g.snd_win_states (g.state_on_turn f_strat s_strat (t+1))
  d : g.draw_states (g.state_on_turn f_strat s_strat t) → g.draw_states (g.state_on_turn f_strat s_strat (t+1))

def Game_World_wDraw.coherent_end (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat : Strategy α β, ∀ t : ℕ, g.coherent_end_aux f_strat s_strat t




-- # Carelessness

def careless (obj : α → List β → γ) (swap : α → List β → β → α): Prop :=
  ∀ ini : α , ∀ hist : List β, ∀ prehist : List β, (h : prehist ≠ []) →
    obj ini (hist ++ prehist) = obj (swap ini prehist.tail (prehist.head h)) hist

lemma careless_singleton (obj : α → List β → γ) (swap : α → List β → β → α) (hc : careless obj swap) :
  ∀ ini : α , ∀ hist : List β, ∀ act : β, obj ini (hist ++ [act]) = obj (swap ini [] (act)) hist
  :=
  by
  intro ini hist act
  apply hc ini hist [act]
  apply List.noConfusion


structure zGame_World_wDraw (α β : Type _) extends Game_World_wDraw α β where
  f_law_careless : careless toGame_World_wDraw.fst_legal toGame_World_wDraw.fst_transition
  s_law_careless : careless toGame_World_wDraw.snd_legal toGame_World_wDraw.fst_transition
  f_transition_careless : careless toGame_World_wDraw.fst_transition toGame_World_wDraw.fst_transition
  s_transition_careless : careless toGame_World_wDraw.snd_transition toGame_World_wDraw.fst_transition
  coherent : toGame_World_wDraw.coherent_end
  sym_trans : toGame_World_wDraw.fst_transition = toGame_World_wDraw.snd_transition



instance (l : List α): Decidable (l = []) :=
  by
  match l with
  | [] => apply isTrue ; rfl
  | x :: L => apply isFalse ; exact List.cons_ne_nil x L



def fst_strat_deconditioned (s_strat : Strategy α β) (f_act : β) (g : Game_World_wDraw α β) : Strategy α β :=
  (fun _ hist => if hist = [] then f_act else s_strat (g.world_after_fst f_act).init_game_state (hist.dropLast))

def snd_strat_deconditioned (f_strat : Strategy α β) (f_act : β) (g : Game_World_wDraw α β) : Strategy α β :=
  (fun _ hist => f_strat (g.world_after_fst f_act).init_game_state (hist.dropLast))

lemma Game_World_wDraw.History_of_deconditioned
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  History_on_turn g.init_game_state fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) ++ [fst_act] :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [History_on_turn, Turn_fst]
    rw [if_pos (by decide), fst_strat_deconditioned, if_pos (by rfl)]
  · dsimp only [History_on_turn] at *
    by_cases q : Turn_fst (t+1)
    · rw [Turn_fst_not_step] at q
      rw [if_neg q] at *
      rw [← Turn_fst_not_step] at q
      rw [if_pos q, if_pos q] at *
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Game_World_wDraw.world_after_fst_init] at ih
      rw [ih]
      rw [snd_strat_deconditioned, List.dropLast_concat]
    · rw [if_neg q, if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q] at *
      rw [fst_strat_deconditioned, snd_strat_deconditioned, if_neg (by apply List.cons_ne_nil)]
      rw [List.cons_append, ← ih]
      congr
      dsimp [snd_strat_deconditioned] at ih
      rw [← Game_World_wDraw.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]



def Game_World_wDraw.transition_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.snd_transition (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.fst_transition g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Game_World_wDraw.transition_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.fst_transition (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.snd_transition g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Game_World_wDraw.transition_blind (g : Game_World_wDraw α β) : Prop :=
 g.transition_blind_fst ∧ g.transition_blind_snd


def Game_World_wDraw.strong_transition_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.snd_transition (g.world_after_fst fst_act).init_game_state hist act
    = g.fst_transition g.init_game_state (hist ++ [fst_act]) act

def Game_World_wDraw.strong_transition_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.fst_transition (g.world_after_fst fst_act).init_game_state hist act
    = g.snd_transition g.init_game_state (hist ++ [fst_act]) act


def Game_World_wDraw.strong_transition_blind (g : Game_World_wDraw α β) : Prop :=
 g.strong_transition_blind_fst ∧ g.strong_transition_blind_snd

lemma Game_World_wDraw.strong_transition_blind_toWeak (g : Game_World_wDraw α β) :
  g.strong_transition_blind → g.transition_blind :=
  by
  rintro ⟨f_strong, s_strong⟩
  constructor
  · intro f_strat s_strat f_act f_act_leg fst_strat snd_strat t act
    rw [Game_World_wDraw.History_of_deconditioned]
    apply f_strong
    exact f_act_leg
  · intro f_strat s_strat f_act f_act_leg fst_strat snd_strat t act
    rw [Game_World_wDraw.History_of_deconditioned]
    apply s_strong
    exact f_act_leg



def Game_World_wDraw.world_after_preHist {α β : Type u} (g : Game_World_wDraw α β)
  (prehist : List β) : Game_World_wDraw α β := -- act not required to be legal
  match prehist with
  | [] => g
  | last :: L => {g with init_game_state := g.fst_transition g.init_game_state L last}



def Game_World_wDraw.hyper_transition_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.fst_legal g.snd_legal g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.snd_transition (g.world_after_preHist prehist).init_game_state hist act
    = g.fst_transition g.init_game_state (hist ++ prehist) act

def Game_World_wDraw.hyper_transition_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.fst_legal g.snd_legal g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.fst_transition (g.world_after_preHist prehist).init_game_state hist act
    = g.snd_transition g.init_game_state (hist ++ prehist) act


def Game_World_wDraw.hyper_transition_blind (g : Game_World_wDraw α β) : Prop :=
 g.hyper_transition_blind_fst ∧ g.hyper_transition_blind_snd


lemma Game_World_wDraw.hyper_transition_blind_transition_eq (g : Game_World_wDraw α β) :
  g.hyper_transition_blind → (g.fst_transition g.init_game_state = g.snd_transition g.init_game_state) :=
  by
  intro h
  have := h.2 [] (by apply Hist_legal.nil)
  dsimp [Game_World_wDraw.world_after_preHist] at this
  simp_rw [List.append_nil] at this
  apply funext₂
  exact this


lemma Game_World_wDraw.hyper_transition_blind_toStrong (g : Game_World_wDraw α β) :
  g.hyper_transition_blind → g.strong_transition_blind :=
  by
  rintro ⟨f_hyper, s_hyper⟩
  constructor
  · intro f_act f_leg hist act
    specialize f_hyper [f_act] _ hist act
    · apply Hist_legal.cons
      · dsimp
        rw [if_pos (by decide)]
        exact f_leg
      · apply Hist_legal.nil
    · dsimp [Game_World_wDraw.world_after_fst, Game_World_wDraw.world_after_preHist] at *
      exact f_hyper
  · intro f_act f_leg hist act
    specialize s_hyper [f_act] _ hist act
    · apply Hist_legal.cons
      · dsimp
        rw [if_pos (by decide)]
        exact f_leg
      · apply Hist_legal.nil
    · dsimp [Game_World_wDraw.world_after_fst, Game_World_wDraw.world_after_preHist] at *
      exact s_hyper

@[simp]
lemma Game_World_wDraw.world_after_preHist_singleton {α β : Type u} (g : Game_World_wDraw α β)
  (act : β) : g.world_after_preHist [act] = g.world_after_fst act :=
  by
  dsimp [Game_World_wDraw.world_after_fst, Game_World_wDraw.world_after_preHist]


lemma zGame_World_wDraw.is_hyper_transition_blind (g : zGame_World_wDraw α β) :
  g.toGame_World_wDraw.hyper_transition_blind :=
  by
  constructor
  · intro prehist preh_leg hist act
    have := g.f_transition_careless g.init_game_state hist prehist
    have that := g.sym_trans
    match prehist with
    | [] =>
        dsimp [Game_World_wDraw.world_after_preHist]
        rw [List.append_nil, that]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this, that]
        dsimp [Game_World_wDraw.world_after_preHist]
        nth_rewrite 1 [that]
        rfl
  · intro prehist preh_leg hist act
    have := g.s_transition_careless g.init_game_state hist prehist
    have that := g.sym_trans
    match prehist with
    | [] =>
        dsimp [Game_World_wDraw.world_after_preHist]
        rw [List.append_nil, that]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this, that]
        dsimp [Game_World_wDraw.world_after_preHist]
        nth_rewrite 1 [that]
        rfl


lemma Game_World_wDraw.State_of_deconditioned
  (g: Game_World_wDraw α β)
  (tb : g.transition_blind)
  (fst_act: β)
  (fst_act_legal: g.fst_legal g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  g.state_on_turn fst_strat snd_strat (turn + 1) =
  (g.world_after_fst fst_act).state_on_turn f_strat s_strat turn :=
  by
  intro fst_strat snd_strat
  cases' turn with t
  · dsimp [state_on_turn]
    rw [if_pos (by decide)]
    dsimp [history_on_turn, History_on_turn]
    rw [fst_strat_deconditioned, if_pos (by rfl)]
  · dsimp [state_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q]
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      dsimp [history_on_turn]
      have := g.History_of_deconditioned fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [snd_strat_deconditioned, List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.2 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (f_strat (world_after_fst g fst_act).toGame_World.init_game_state (History_on_turn (world_after_fst g fst_act).toGame_World.init_game_state f_strat s_strat t))
      rw [← Game_World_wDraw.world_after_fst_init]
      rw [← this]
      clear this
      rfl
    · rw [Turn_not_fst_iff_snd, Turn_snd_fst_step] at q
      rw [if_pos q]
      dsimp [history_on_turn]
      rw [← Turn_fst_step, Turn_fst_not_step] at q
      rw [if_neg q]
      rw [fst_strat_deconditioned, if_neg (by apply History_on_turn_nonempty_of_succ)]
      have := g.History_of_deconditioned fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.1 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (s_strat (world_after_fst g fst_act).toGame_World.init_game_state (History_on_turn (Game_World.fst_transition g.toGame_World g.init_game_state [] fst_act) f_strat s_strat t))
      rw [← Game_World_wDraw.world_after_fst_init] at this
      rw [← Game_World_wDraw.world_after_fst_init]
      rw [← this]


-- State_of_deconditioned for zGame
-- then for ↓ use ∀ in coherent_end of (g : zGame) to get coherence

#exit

def zGame_World_wDraw.world_after_fst {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) : zGame_World_wDraw α β := -- act not required to be legal
  {(g.toGame_World_wDraw.world_after_fst fst_act) with
      f_law_careless := by dsimp ; apply g.f_law_careless
      s_law_careless := by dsimp ; apply g.s_law_careless
      f_transition_careless := by dsimp ; apply g.f_transition_careless
      s_transition_careless := by dsimp ; apply g.s_transition_careless
      coherent := by
                  intro f_strat s_strat t
                  constructor
                  · intro fws
                    dsimp at *
                    rw [Game_World_wDraw.state_on_turn_toGame_World] at *
                    dsimp at *
                    rw [Game_World_wDraw.state_world_after_fst]

                  }


#exit


lemma Game_World_wDraw.world_after_preHist_transition_blind
  (g : Game_World_wDraw α β) (hg : g.hyper_transition_blind) (f_act : β) (f_leg : g.fst_legal g.init_game_state [] f_act) :
  (g.world_after_fst f_act).hyper_transition_blind :=
  by
  have shg := g.hyper_transition_blind_toStrong hg
  have teq := g.hyper_transition_blind_transition_eq hg
  constructor
  · intro prehist preh_leg hist act
    obtain ⟨hgf, hgs⟩ := hg
    obtain ⟨shgf, shgs⟩ := shg
    specialize hgf (prehist ++ [f_act]) _ hist act
    · sorry -- might need some sort of hyper legality for this
    · rw [Game_World_wDraw.world_after_fst_snd_transition, Game_World_wDraw.world_after_fst_fst_transition]
      specialize shgs f_act f_leg (hist ++ prehist) act
      rw [shgs]
      nth_rewrite 1 [← teq]
      rw [List.append_assoc]
      rw [← hgf]
      dsimp [Game_World_wDraw.world_after_fst, Game_World_wDraw.world_after_preHist]
      cases' prehist with x L
      · dsimp
      · dsimp

#exit




#exit

lemma Game_World_wDraw.fst_legal_preconditioned'
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (s_leg: Strategy_legal_snd (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).snd_legal) f_strat s_strat)
  (b : g.law_blind_fst')
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal_fst g.init_game_state (fun x => g.fst_legal) fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · dsimp [History_on_turn]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · rw [← b, Game_World_wDraw.History_of_preconditioned']
    · dsimp [History_on_turn]
      rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil fst_act [])]
      rw [List.dropLast_concat]
      apply s_leg
      rw [Turn_snd_fst_step]
      exact tf
    · exact fst_act_legal


lemma Game_World_wDraw.snd_legal_preconditioned'
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (f_leg: Strategy_legal_fst (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).fst_legal) f_strat s_strat)
  (b : g.law_blind_snd')
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal_snd g.init_game_state (fun x => g.snd_legal) fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · contradiction
  · rw [← b, Game_World_wDraw.History_of_preconditioned']
    · dsimp [History_on_turn]
      rw [List.dropLast_concat]
      apply f_leg
      rw [Turn_fst_snd_step]
      exact tf
    · exact fst_act_legal
