/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic




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




structure zGame_World_wDraw (α β : Type _) extends Game_World_wDraw α β where
  f_legal_careless : careless toGame_World_wDraw.fst_legal toGame_World_wDraw.fst_transition
  s_legal_careless : careless toGame_World_wDraw.snd_legal toGame_World_wDraw.fst_transition
  f_transition_careless : careless toGame_World_wDraw.fst_transition toGame_World_wDraw.fst_transition
  s_transition_careless : careless toGame_World_wDraw.snd_transition toGame_World_wDraw.fst_transition
  coherent : toGame_World_wDraw.coherent_end
  sym_trans : toGame_World_wDraw.fst_transition = toGame_World_wDraw.snd_transition
  sym_legal : toGame_World_wDraw.fst_legal = toGame_World_wDraw.snd_legal
  sym_win : toGame_World_wDraw.fst_win_states = toGame_World_wDraw.snd_win_states



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


lemma zGame_World_wDraw.State_of_deconditioned
  (g: zGame_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned s_strat fst_act g.toGame_World_wDraw
  let snd_strat := snd_strat_deconditioned f_strat fst_act g.toGame_World_wDraw
  g.state_on_turn fst_strat snd_strat (turn + 1) =
  (g.world_after_fst fst_act).state_on_turn f_strat s_strat turn :=
  by
  apply Game_World_wDraw.State_of_deconditioned
  · apply Game_World_wDraw.strong_transition_blind_toWeak
    apply Game_World_wDraw.hyper_transition_blind_toStrong
    apply zGame_World_wDraw.is_hyper_transition_blind
  · exact fst_act_legal



def zGame_World_wDraw.world_after_fst {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) : zGame_World_wDraw α β :=
  {(g.toGame_World_wDraw.world_after_fst fst_act) with
      f_legal_careless := by dsimp ; apply g.f_legal_careless
      s_legal_careless := by dsimp ; apply g.s_legal_careless
      f_transition_careless := by dsimp ; apply g.f_transition_careless
      s_transition_careless := by dsimp ; apply g.s_transition_careless
      sym_trans := by dsimp ; apply g.sym_trans
      sym_legal := by dsimp ; apply g.sym_legal
      sym_win := by dsimp ; apply g.sym_win
      coherent := by
                  intro f_strat s_strat t
                  constructor
                  · intro fws
                    dsimp at *
                    rw [Game_World_wDraw.state_on_turn_toGame_World] at *
                    dsimp at *
                    rw [← Game_World_wDraw.state_on_turn_toGame_World] at *
                    rw [← g.State_of_deconditioned fst_act fst_act_legal f_strat s_strat] at *
                    have := (g.coherent (fst_strat_deconditioned s_strat fst_act g.toGame_World_wDraw) (snd_strat_deconditioned f_strat fst_act g.toGame_World_wDraw) (t+1)).f
                    exact this fws
                  · intro fws
                    dsimp at *
                    rw [Game_World_wDraw.state_on_turn_toGame_World] at *
                    dsimp at *
                    rw [← Game_World_wDraw.state_on_turn_toGame_World] at *
                    rw [← g.State_of_deconditioned fst_act fst_act_legal f_strat s_strat] at *
                    have := (g.coherent (fst_strat_deconditioned s_strat fst_act g.toGame_World_wDraw) (snd_strat_deconditioned f_strat fst_act g.toGame_World_wDraw) (t+1)).s
                    exact this fws
                  · intro fws
                    dsimp at *
                    rw [Game_World_wDraw.state_on_turn_toGame_World] at *
                    dsimp at *
                    rw [← Game_World_wDraw.state_on_turn_toGame_World] at *
                    rw [← g.State_of_deconditioned fst_act fst_act_legal f_strat s_strat] at *
                    have := (g.coherent (fst_strat_deconditioned s_strat fst_act g.toGame_World_wDraw) (snd_strat_deconditioned f_strat fst_act g.toGame_World_wDraw) (t+1)).d
                    exact this fws

                  }


lemma zGame_World_wDraw.world_after_fst_init (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).init_game_state = g.fst_transition g.init_game_state [] fst_act :=
  by
  rfl



-- # Careless strat


def Game_World_wDraw.Strategy_blind_fst (strat : Strategy α β) (g : Game_World_wDraw α β) : Prop :=
  ∀ s_strat: Strategy α β,
  let fst_act := strat g.init_game_state []
  ∀ turn : ℕ, strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state s_strat strat turn)
    = strat g.init_game_state (History_on_turn g.init_game_state strat s_strat (turn + 1))


def Game_World_wDraw.Strategy_blind_snd (strat : Strategy α β) (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat: Strategy α β,
  let fst_act := f_strat g.init_game_state []
  ∀ turn : ℕ, strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state strat f_strat turn)
    = strat g.init_game_state (History_on_turn g.init_game_state f_strat strat (turn + 1))

def Game_World_wDraw.Strategy_blind (strat : Strategy α β) (g : Game_World_wDraw α β) : Prop :=
  g.Strategy_blind_fst strat ∧ g.Strategy_blind_snd strat

def Game_World_wDraw.strong_Strategy_blind (strat : Strategy α β) (g : Game_World_wDraw α β) : Prop :=
  ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  ∀ hist : List β, strat (g.world_after_fst fst_act).init_game_state hist
    = strat g.init_game_state (hist ++ [fst_act])

lemma Game_World_wDraw.world_after_fst_History_blind (g : Game_World_wDraw α β)
  (f_strat s_strat : Strategy α β) (turn : ℕ)
  (hf : g.Strategy_blind_fst f_strat) (hs : g.Strategy_blind_snd s_strat)
  :
  (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn)
  ++ [(f_strat g.init_game_state [])] = History_on_turn g.init_game_state f_strat s_strat (turn+1) :=
  by
  rw [History_on_turn]
  induction' turn with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by decide)]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t+1)
    · rw [if_pos q] at *
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      rw [← Turn_fst_not_step] at q
      rw [if_pos q]
      rw [Game_World_wDraw.world_after_fst_init] at *
      rw [List.cons_append, ih]
      congr 1
      have := hs f_strat t
      rw [← Game_World_wDraw.world_after_fst_init, this]
      dsimp [History_on_turn]
      rw [if_pos q]
    · rw [if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q]
      rw [← @not_not (Turn_fst (t + 1 + 1)), ← Turn_fst_not_step] at q
      rw [if_neg q]
      rw [Game_World_wDraw.world_after_fst_init] at *
      rw [List.cons_append]
      congr 1
      have := hf s_strat t
      rw [Game_World_wDraw.world_after_fst_init] at this
      rw [this]
      dsimp [History_on_turn]
      rw [if_neg q]


lemma Game_World_wDraw.world_after_fst_History_strong_blind (g : Game_World_wDraw α β)
  (f_strat s_strat : Strategy α β) (turn : ℕ)
  (f_leg : Strategy_legal_fst g.init_game_state g.fst_legal f_strat s_strat)
  (hf : g.strong_Strategy_blind f_strat) (hs : g.strong_Strategy_blind s_strat)
  :
  (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn)
  ++ [(f_strat g.init_game_state [])] = History_on_turn g.init_game_state f_strat s_strat (turn+1) :=
  by
  rw [History_on_turn]
  induction' turn with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by decide)]
  · unfold History_on_turn
    by_cases q : Turn_fst (t+1)
    · rw [if_pos q]
      rw [List.cons_append, ih]
      specialize hs (f_strat g.init_game_state []) (by apply f_leg 0 (by decide)) (History_on_turn (Game_World.fst_transition g.toGame_World g.init_game_state [] (f_strat g.init_game_state [])) s_strat f_strat t)
      rw [← Game_World_wDraw.world_after_fst_init] at hs
      rw [hs, ih]
      rw [if_neg (show ¬ Turn_fst (Nat.succ t + 1) from (by rw [← Turn_fst_not_step]; exact q))]
    · rw [if_neg q]
      rw [List.cons_append, ih]
      specialize hf (f_strat g.init_game_state []) (by apply f_leg 0 (by decide)) (History_on_turn (Game_World.fst_transition g.toGame_World g.init_game_state [] (f_strat g.init_game_state [])) s_strat f_strat t)
      rw [← Game_World_wDraw.world_after_fst_init] at hf
      rw [hf, ih]
      rw [if_pos (show Turn_fst (Nat.succ t + 1) from (by rw [iff_not_comm.mp (Turn_fst_not_step (t+1))]; exact q))]


-- might not be the case, because we have no carelessness of other strat
-- lemma Game_World_wDraw.strong_Strategy_blind_toWeak (strat : Strategy α β) (g : Game_World_wDraw α β)
--   (f_leg : Strategy_legal_fst g.init_game_state g.fst_legal strat s_strat) :
--   g.strong_Strategy_blind strat → g.Strategy_blind strat :=
--   by
--   intro hyp
--   constructor
--   · intro s_strat f_act t
--     rw [hyp]



--#exit

def Game_World_wDraw.hyper_Strategy_blind
  (strat : Strategy α β) (g : Game_World_wDraw α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.fst_legal g.snd_legal g.init_game_state prehist →
  ∀ hist : List β, strat (g.world_after_preHist prehist).init_game_state hist
    = strat g.init_game_state (hist ++ prehist)


lemma Game_World_wDraw.hyper_Strategy_blind_toStrong
  (strat : Strategy α β) (g : Game_World_wDraw α β) :
  g.hyper_Strategy_blind strat → g.strong_Strategy_blind strat :=
  by
  intro hyp
  intro f_act f_leg hist
  specialize hyp [f_act] _ hist
  · apply Hist_legal.cons
    · dsimp
      rw [if_pos (by decide)]
      exact f_leg
    · apply Hist_legal.nil
  · dsimp [Game_World_wDraw.world_after_fst, Game_World_wDraw.world_after_preHist] at *
    exact hyp


--#exit

-- # Blind law

def Game_World_wDraw.legal_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.snd_legal (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.fst_legal g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Game_World_wDraw.legal_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.fst_legal (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.snd_legal g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Game_World_wDraw.legal_blind (g : Game_World_wDraw α β) : Prop :=
 g.legal_blind_fst ∧ g.legal_blind_snd


def Game_World_wDraw.strong_legal_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.snd_legal (g.world_after_fst fst_act).init_game_state hist act
    = g.fst_legal g.init_game_state (hist ++ [fst_act]) act

def Game_World_wDraw.strong_legal_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ fst_act : β, g.fst_legal g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.fst_legal (g.world_after_fst fst_act).init_game_state hist act
    = g.snd_legal g.init_game_state (hist ++ [fst_act]) act


def Game_World_wDraw.strong_legal_blind (g : Game_World_wDraw α β) : Prop :=
 g.strong_legal_blind_fst ∧ g.strong_legal_blind_snd

lemma Game_World_wDraw.strong_legal_blind_toWeak (g : Game_World_wDraw α β) :
  g.strong_legal_blind → g.legal_blind :=
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




def Game_World_wDraw.hyper_legal_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.fst_legal g.snd_legal g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.snd_legal (g.world_after_preHist prehist).init_game_state hist act
    = g.fst_legal g.init_game_state (hist ++ prehist) act

def Game_World_wDraw.hyper_legal_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.fst_legal g.snd_legal g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.fst_legal (g.world_after_preHist prehist).init_game_state hist act
    = g.snd_legal g.init_game_state (hist ++ prehist) act


def Game_World_wDraw.hyper_legal_blind (g : Game_World_wDraw α β) : Prop :=
 g.hyper_legal_blind_fst ∧ g.hyper_legal_blind_snd


lemma Game_World_wDraw.hyper_legal_blind_legal_eq (g : Game_World_wDraw α β) :
  g.hyper_legal_blind → (g.fst_legal g.init_game_state = g.snd_legal g.init_game_state) :=
  by
  intro h
  have := h.2 [] (by apply Hist_legal.nil)
  dsimp [Game_World_wDraw.world_after_preHist] at this
  simp_rw [List.append_nil] at this
  apply funext₂
  exact this


lemma Game_World_wDraw.hyper_legal_blind_toStrong (g : Game_World_wDraw α β) :
  g.hyper_legal_blind → g.strong_legal_blind :=
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


lemma zGame_World_wDraw.is_hyper_legal_blind (g : zGame_World_wDraw α β) :
  g.toGame_World_wDraw.hyper_legal_blind :=
  by
  constructor
  · intro prehist preh_leg hist act
    have := g.f_legal_careless g.init_game_state hist prehist
    have that := g.sym_legal
    match prehist with
    | [] =>
        dsimp [Game_World_wDraw.world_after_preHist]
        rw [List.append_nil, that]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this, that]
        dsimp [Game_World_wDraw.world_after_preHist]
  · intro prehist preh_leg hist act
    have := g.s_legal_careless g.init_game_state hist prehist
    have that := g.sym_legal
    match prehist with
    | [] =>
        dsimp [Game_World_wDraw.world_after_preHist]
        rw [List.append_nil, that]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this, that]
        dsimp [Game_World_wDraw.world_after_preHist]



lemma Game_World_wDraw.fst_legal_deconditioned
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (s_leg: Strategy_legal_snd (g.world_after_fst fst_act).init_game_state (g.world_after_fst fst_act).snd_legal f_strat s_strat)
  (b : g.legal_blind_fst)
  :
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  Strategy_legal_fst g.init_game_state g.fst_legal fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · dsimp [History_on_turn, fst_strat_deconditioned]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · rw [← b, Game_World_wDraw.History_of_deconditioned]
    · dsimp [History_on_turn, fst_strat_deconditioned]
      rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil fst_act [])]
      rw [List.dropLast_concat]
      apply s_leg
      rw [Turn_snd_fst_step]
      exact tf
    · exact fst_act_legal


lemma Game_World_wDraw.snd_legal_deconditioned
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (f_leg: Strategy_legal_fst (g.world_after_fst fst_act).init_game_state (g.world_after_fst fst_act).fst_legal f_strat s_strat)
  (b : g.legal_blind_snd)
  :
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  Strategy_legal_snd g.init_game_state g.snd_legal fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · contradiction
  · rw [← b, Game_World_wDraw.History_of_deconditioned]
    · dsimp [History_on_turn, snd_strat_deconditioned]
      rw [List.dropLast_concat]
      apply f_leg
      rw [Turn_fst_snd_step]
      exact tf
    · exact fst_act_legal




-- keep as exit ?
#exit

lemma Game_World.Strategy_careless_act_on_turn_snd (g : Game_World α β) (f_strat s_strat: Strategy α β)
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat) (turn : ℕ) :
  s_strat (g.world_after_fst (f_strat g.init_game_state [])).init_game_state
    (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) =
  s_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) :=
  by
  rw [Game_World.world_after_fst_init, hs]
  congr
  apply Game_World.world_after_fst_History g f_strat s_strat turn hs hf



lemma Game_World.Strategy_careless_act_on_turn_fst
  (g : zGame_World_wDraw α β)
  (f_strat s_strat: Strategy α β)
  (h : Strategy_legal_fst g.init_game_state g.fst_legal f_strat s_strat)
  (hf : careless f_strat g.fst_transition) (hs : careless s_strat g.fst_transition) (turn : ℕ) :
  f_strat (g.world_after_fst (f_strat g.init_game_state []) (by apply h 0 (by decide))).init_game_state
    (History_on_turn (g.world_after_fst (f_strat g.init_game_state []) (by apply h 0 (by decide))).init_game_state s_strat f_strat turn) =
  f_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) :=
  by
  specialize hf g.init_game_state
  dsimp [careless] at hf
  rw [zGame_World_wDraw.world_after_fst_init, hf]
  congr
  apply Game_World.world_after_fst_History g f_strat s_strat turn hs hf


lemma Game_World.world_after_fst_legal
  (g : zGame_World_wDraw α β)
  (f_strat s_strat: Strategy α β)
  (h : Strategy_legal_fst g.init_game_state g.fst_legal f_strat s_strat)
  (hf : careless f_strat g.fst_transition) (hs : careless s_strat g.fst_transition) :
  Strategy_legal_snd (g.world_after_fst (f_strat g.init_game_state []) (by apply h 0 (by decide))).init_game_state g.snd_legal s_strat f_strat :=
  by
  dsimp [Strategy_legal_snd] at *
  intro t
  have := g.Strategy_careless_act_on_turn_fst f_strat s_strat hs hf t
  rw [Game_World.world_after_fst_init] at this
  rw [this]
  clear this
  obtain ⟨bf, bs⟩ := hg
  specialize h (t+1)
  specialize bf t (f_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (t + 1)))
  rw [← Game_World.world_after_fst_init, bf]
  exact h

#exit

lemma Game_World.world_after_snd_legal (g : Game_World α β)
   (f_strat s_strat: Strategy α β) (h : Strategy_legal g.init_game_state (fun x => g.snd_legal) f_strat s_strat s_strat)
   (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
   (hg : g.law_blind f_strat s_strat):
   Strategy_legal (g.world_after_fst (f_strat g.init_game_state [])).init_game_state (fun x => (g.world_after_fst (f_strat g.init_game_state [])).fst_legal) s_strat f_strat s_strat :=
   by
   dsimp [Strategy_legal] at *
   intro t
   have := g.Strategy_careless_act_on_turn_snd f_strat s_strat hs hf t
   rw [Game_World.world_after_fst_init] at this
   rw [this]
   clear this
   obtain ⟨bf, bs⟩ := hg
   specialize h (t+1)
   specialize bs t (s_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (t + 1)))
   rw [← Game_World.world_after_fst_init, bs]
   exact h
