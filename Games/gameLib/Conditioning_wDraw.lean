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



-- # Playability


/--
Remember that the game goes on even when its over, where players
play dummy values, in our formalism (and coherent end assures certain props)
The ∀ initial states may seem to strong, but its necessary for world_after_fst
and is also explain by playing dummy vals, in a a priori impossible initial state
-/
def law_nonprohibitive (law : α → List β → β → Prop) : Prop :=
  ∀ ini : α, ∀ hist : List β, ∃ act : β, law ini hist act

def Game_World_wDraw.playable (g : Game_World_wDraw α β) : Prop :=
  law_nonprohibitive g.fst_legal ∧ law_nonprohibitive g.snd_legal

lemma Game_World_wDraw.playable_has_strat (g : Game_World_wDraw α β)
  (hg : g.playable) :
  ∃ f_strat : Strategy α β , ∃ s_strat : Strategy α β,
  Strategy_legal_fst g.init_game_state g.fst_legal f_strat s_strat ∧
  Strategy_legal_snd g.init_game_state g.snd_legal f_strat s_strat :=
  by
  classical
  use (fun ini hist => Classical.choose (hg.1 ini hist))
  use (fun ini hist => Classical.choose (hg.2 ini hist))
  constructor
  · intro t _
    set hist := (History_on_turn g.init_game_state
    (fun ini hist => Classical.choose (_ : ∃ act, Game_World.fst_legal g.toGame_World ini hist act))
    (fun ini hist => Classical.choose (_ : ∃ act, Game_World.snd_legal g.toGame_World ini hist act)) t)
    have pf := Classical.choose_spec (hg.1 g.init_game_state hist)
    apply pf
  · intro t _
    set hist := (History_on_turn g.init_game_state
    (fun ini hist => Classical.choose (_ : ∃ act, Game_World.fst_legal g.toGame_World ini hist act))
    (fun ini hist => Classical.choose (_ : ∃ act, Game_World.snd_legal g.toGame_World ini hist act)) t)
    have ps:= Classical.choose_spec (hg.2 g.init_game_state hist)
    apply ps




lemma Game_World_wDraw.has_WLD_init_end
  (g : Game_World_wDraw α β)
  (hg : g.playable)
  (P : Prop)
  (hp : P)
  (h : (P ∧ ((¬ g.draw_states g.init_game_state) ∧ (¬ g.snd_win_states g.init_game_state))) → g.has_WLD) :
  g.has_WLD :=
  by
  obtain ⟨fs,ss,_,_⟩ := g.playable_has_strat hg
  by_cases q1 : g.draw_states g.init_game_state
  · apply Game_World_wDraw.has_WLD.d
    right
    use fs
    intro _ _ _
    use 0
    constructor
    · decide
    · constructor
      · dsimp [Game_wDraw.state_on_turn]
        exact q1
      · intro n no
        contradiction
  · by_cases q2 : g.snd_win_states g.init_game_state
    · apply Game_World_wDraw.has_WLD.ws
      use fs
      intro _ _ _
      use 0
      constructor
      · decide
      · constructor
        · dsimp [Game_wDraw.state_on_turn]
          exact q2
        · intro n no
          contradiction
    · exact h ⟨hp, q1, q2⟩





-- # zGame

structure zGame_World_wDraw (α β : Type _) extends Game_World_wDraw α β where
  f_legal_careless : careless toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_legal toGame_World_wDraw.fst_transition
  s_legal_careless : careless toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.snd_legal toGame_World_wDraw.fst_transition
  f_transition_careless : careless toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.fst_transition toGame_World_wDraw.fst_transition
  s_transition_careless : careless toGame_World_wDraw.fst_legal toGame_World_wDraw.snd_legal toGame_World_wDraw.init_game_state toGame_World_wDraw.snd_transition toGame_World_wDraw.fst_transition
  coherent : toGame_World_wDraw.coherent_end
  playable : toGame_World_wDraw.playable
  sym_trans : toGame_World_wDraw.fst_transition = toGame_World_wDraw.snd_transition
  sym_legal : toGame_World_wDraw.fst_legal = toGame_World_wDraw.snd_legal
  sym_win : toGame_World_wDraw.fst_win_states = toGame_World_wDraw.snd_win_states


structure zGame_wDraw (α β : Type _) extends zGame_World_wDraw α β where
  /-- The first players strategy-/
  fst_strat : Strategy α β
  /-- The second players strategy-/
  snd_strat : Strategy α β
  /-- The first players strategy is legal wrt. `fst_legal` and the second strategy-/
  fst_lawful : Strategy_legal_fst init_game_state fst_legal fst_strat snd_strat
  /-- The second players strategy is legal wrt. `snd_legal` and the first strategy-/
  snd_lawful : Strategy_legal_snd init_game_state snd_legal fst_strat snd_strat



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
        · dsimp [Game_World_wDraw.world_after_preHist]
          nth_rewrite 1 [that]
          rfl
        · exact preh_leg
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
        · dsimp [Game_World_wDraw.world_after_preHist]
          nth_rewrite 1 [that]
          rfl
        · exact preh_leg


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
      playable := by
                  constructor
                  · dsimp
                    apply g.playable.1
                  · dsimp
                    apply g.playable.2
                  }


lemma zGame_World_wDraw.world_after_fst_init (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).init_game_state = g.fst_transition g.init_game_state [] fst_act :=
  by
  rfl


@[simp]
lemma zGame_World_wDraw.world_after_fst_fst_legal {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).fst_legal = g.fst_legal :=
  by rfl

@[simp]
lemma zGame_World_wDraw.world_after_fst_snd_legal {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).snd_legal = g.snd_legal :=
  by rfl

@[simp]
lemma zGame_World_wDraw.world_after_fst_fst_win_states {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).fst_win_states = g.fst_win_states :=
  by rfl


@[simp]
lemma zGame_World_wDraw.world_after_fst_snd_win_states {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).snd_win_states = g.snd_win_states :=
  by rfl

@[simp]
lemma zGame_World_wDraw.world_after_fst_draw_states {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).draw_states = g.draw_states :=
  by rfl

@[simp]
lemma zGame_World_wDraw.world_after_fst_fst_transition {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).fst_transition = g.fst_transition :=
  by rfl

@[simp]
lemma zGame_World_wDraw.world_after_fst_snd_transition {α β : Type u} (g : zGame_World_wDraw α β)
  (fst_act : β) (fst_act_legal: g.fst_legal g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).snd_transition = g.snd_transition :=
  by rfl



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
        · dsimp [Game_World_wDraw.world_after_preHist]
        · exact preh_leg
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
        · dsimp [Game_World_wDraw.world_after_preHist]
        · exact preh_leg



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


def zGame_wDraw.history_on_turn {α β : Type u} (g : zGame_wDraw α β) : ℕ → List β :=
  History_on_turn g.init_game_state g.fst_strat g.snd_strat


def zGame_wDraw.state_on_turn {α β : Type u} (g : zGame_wDraw α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn n
         if Turn_fst (n+1)
         then g.fst_transition g.init_game_state h (g.fst_strat g.init_game_state h)
         else g.snd_transition g.init_game_state h (g.snd_strat g.init_game_state h)





-- # Termination



def zGame_wDraw.fst_win  {α β : Type _} (g : zGame_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn ∧ g.fst_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral g.fst_strat g.snd_strat t)


def zGame_wDraw.snd_win  {α β : Type u} (g : zGame_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.snd_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral g.fst_strat g.snd_strat t)


def zGame_wDraw.fst_draw {α β : Type u} (g : zGame_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn  ∧ g.draw_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral g.fst_strat g.snd_strat t)


def zGame_wDraw.snd_draw {α β : Type u} (g : zGame_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.draw_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral g.fst_strat g.snd_strat t)


def zGame_wDraw.draw {α β : Type u} (g : zGame_wDraw α β) : Prop :=
  g.fst_draw ∨ g.snd_draw


def zGame_World_wDraw.is_fst_win  {α β : Type u} (g : zGame_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β, --g.Strategy_blind_fst ws ∧
  ∀ snd_s : Strategy α β, --g.Strategy_blind_fst snd_s →
   (ws_leg : Strategy_legal_fst g.init_game_state g.fst_legal ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state g.snd_legal ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Game_wDraw α β).fst_win


def zGame_World_wDraw.is_snd_win  {α β : Type u} (g : zGame_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β, -- g.Strategy_blind_snd ws ∧
  ∀ fst_s : Strategy α β, --g.Strategy_blind_snd fst_s →
   (ws_leg : Strategy_legal_snd g.init_game_state g.snd_legal fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state g.fst_legal fst_s ws) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Game_wDraw α β).snd_win

def zGame_World_wDraw.is_fst_draw  {α β : Type u} (g : zGame_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β, -- g.Strategy_blind_fst ws ∧
  ∀ snd_s : Strategy α β, -- g.Strategy_blind_fst snd_s →
   (ws_leg : Strategy_legal_fst g.init_game_state g.fst_legal ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state g.snd_legal ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Game_wDraw α β).fst_draw


def zGame_World_wDraw.is_snd_draw  {α β : Type u} (g : zGame_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,-- g.Strategy_blind_snd ws ∧
  ∀ fst_s : Strategy α β, -- g.Strategy_blind_snd fst_s →
   (ws_leg : Strategy_legal_snd g.init_game_state g.snd_legal fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state g.fst_legal fst_s ws) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Game_wDraw α β).snd_draw



def zGame_wDraw.is_draw {α β : Type u} (g : zGame_wDraw α β) : Prop :=
  g.is_fst_draw ∨ g.is_snd_draw



inductive zGame_World_wDraw.has_WLD (g : zGame_World_wDraw α β) : Prop where
| wf : g.is_fst_win → g.has_WLD
| ws : g.is_snd_win → g.has_WLD
| d : g.is_draw → g.has_WLD


lemma zGame_World_wDraw.has_WLD_init_end
  (g : zGame_World_wDraw α β)
  (P : Prop)
  (hp : P)
  (h : (P ∧ ((¬ g.draw_states g.init_game_state) ∧ (¬ g.snd_win_states g.init_game_state))) → g.has_WLD) :
  g.has_WLD :=
  by
  obtain ⟨fs,ss,_,_⟩ := g.playable_has_strat g.playable
  by_cases q1 : g.draw_states g.init_game_state
  · apply zGame_World_wDraw.has_WLD.d
    right
    use fs
    intro _ _ _
    use 0
    constructor
    · decide
    · constructor
      · dsimp [Game_wDraw.state_on_turn]
        exact q1
      · intro n no
        contradiction
  · by_cases q2 : g.snd_win_states g.init_game_state
    · apply zGame_World_wDraw.has_WLD.ws
      use fs
      intro _ _ _
      use 0
      constructor
      · decide
      · constructor
        · apply q2
        · intro t no
          contradiction
    · exact h ⟨hp, q1, q2⟩



-- # Easy termination


inductive zGame_World_wDraw.has_WL (g : zGame_World_wDraw α β) : Prop where
| wf : g.is_fst_win → g.has_WL
| ws : g.is_snd_win → g.has_WL


lemma zGame_World_wDraw.has_WL_init_end
  (g : zGame_World_wDraw α β)
  (P : Prop)
  (hp : P)
  (h : (P ∧ (¬ g.snd_win_states g.init_game_state)) → g.has_WL) :
  g.has_WL :=
  by
  obtain ⟨fs,ss,_,_⟩ := g.playable_has_strat g.playable
  by_cases q2 : g.snd_win_states g.init_game_state
  · apply zGame_World_wDraw.has_WL.ws
    use fs
    intro _ _ _
    use 0
    constructor
    · decide
    · constructor
      · apply q2
      · intro t no
        contradiction
  · exact h ⟨hp, q2⟩

--#exit

-- # More conditioining

def zGame_World_wDraw.snd_strat_conditioned (f_strat : Strategy α β) (f_act : β) (g : zGame_World_wDraw α β) : Strategy α β :=
  fun _ hist => f_strat g.init_game_state (hist ++ [f_act])

open Classical

noncomputable
def zGame_World_wDraw.fst_strat_conditioned [Inhabited β] (g : zGame_World_wDraw α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  : Strategy α β :=
  fun (_ : α) hist  =>
    if hh : hist = [] -- shouldn't happen, as snd strat
    then default -- dummy
    else let f_act := List.getLast hist hh
         if H : g.fst_legal g.init_game_state [] f_act-- should be the cases ?!?
         then (f_strat hist hh H) (g.fst_transition g.init_game_state [] f_act) hist.dropLast -- is it ? since ref to history in current game
         else default

lemma zGame_World_wDraw.history_on_turn_conditioned
  [Inhabited β] (g : zGame_World_wDraw α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → (Hl : g.fst_legal g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.fst_legal g.init_game_state [] (fst_s g.init_game_state [])):
  let f_act := fst_s g.init_game_state []
  ∀ t : ℕ,
  g.history_on_turn fst_s (g.fst_strat_conditioned f_strat) (t+1) =
  ((g.world_after_fst f_act f_act_leg).history_on_turn (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) t) ++ [f_act]:=
  by
  intro f_act t
  induction' t with t ih
  · dsimp [Game_World_wDraw.history_on_turn, History_on_turn]
    rw [if_pos (by decide)]
  · dsimp [Game_World_wDraw.history_on_turn, History_on_turn]
    by_cases q : Turn_fst (Nat.succ t + 1)
    · rw [if_pos q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at q
      rw [if_neg q,if_neg q]
      dsimp [zGame_World_wDraw.snd_strat_conditioned]
      unfold Game_World_wDraw.history_on_turn at ih
      rw [← ih]
      dsimp [History_on_turn]
      rw [if_neg q]
    · rw [if_neg q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at q
      rw [if_pos q, if_pos q]
      dsimp [zGame_World_wDraw.fst_strat_conditioned]
      rw [dif_neg (by apply List.cons_ne_nil)]
      have := History_on_turn_getLast_fst_act g.init_game_state fst_s (g.fst_strat_conditioned f_strat) (t)
      dsimp [History_on_turn] at this
      simp_rw [if_pos q] at this
      rw [dif_pos (by rw [this] ; apply f_act_leg)]
      unfold Game_World_wDraw.history_on_turn at ih
      rw [← ih]
      have that : History_on_turn g.init_game_state fst_s (fst_strat_conditioned g f_strat) (t + 1) =
                  (fst_s g.init_game_state (History_on_turn g.init_game_state fst_s (fst_strat_conditioned g f_strat) t) ::
                   History_on_turn g.init_game_state fst_s (fst_strat_conditioned g f_strat) t) :=
        by
        dsimp [History_on_turn]
        rw [if_pos q]
      have thut : List.getLast (History_on_turn g.init_game_state fst_s (g.fst_strat_conditioned f_strat) (t + 1))  (by apply History_on_turn_nonempty_of_succ) = f_act :=
        by
        simp_rw [ih]
        rw [List.getLast_append]
      simp_rw [← that]
      specialize h_f_strat (History_on_turn g.init_game_state fst_s (g.fst_strat_conditioned f_strat) (t + 1)) [f_act]
                  (by apply History_on_turn_nonempty_of_succ) (by apply List.cons_ne_nil)
                  (by rw [thut] ; apply f_act_leg) (by apply f_act_leg)
                  (by apply thut)
      rw [h_f_strat]
      congr
      rw [ih]
      rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)]
      dsimp
      rw [List.append_nil]





lemma zGame_World_wDraw.state_on_turn_conditioned
  [Inhabited β] (g : zGame_World_wDraw α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → (Hl : g.fst_legal g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.fst_legal g.init_game_state [] (fst_s g.init_game_state [])):
  let f_act := fst_s g.init_game_state []
  ∀ t : ℕ,
  g.state_on_turn fst_s (g.fst_strat_conditioned f_strat) (t+1) =
  (g.world_after_fst f_act f_act_leg).state_on_turn (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) t:=
  by
  intro f_act t
  cases' t with t
  · dsimp [Game_World_wDraw.state_on_turn]
    rw [if_pos (by decide)]
    dsimp [Game_World_wDraw.history_on_turn, History_on_turn, zGame_World_wDraw.world_after_fst_init]
  · dsimp [Game_World_wDraw.state_on_turn]
    by_cases q : Turn_fst (t + 1 + 1)
    · rw [if_pos q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at q
      rw [if_neg q]
      rw [g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg]
      have := careless_singleton _ _ _ _ _ (g.f_transition_careless)
      specialize this g.init_game_state ((Game_World_wDraw.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toGame_World_wDraw
          (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
          (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t)) f_act f_act_leg
      simp_rw [this]
      rw [g.sym_trans]
      congr
      rw [← g.sym_trans]
      rfl
    · rw [if_neg q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at q
      rw [if_pos q]
      rw [g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg]
      have := careless_singleton _ _ _ _ _ (g.s_transition_careless)
      specialize this g.init_game_state ((Game_World_wDraw.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toGame_World_wDraw
          (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
          (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t)) f_act f_act_leg
      simp_rw [this]
      rw [← g.sym_trans]
      congr
      dsimp [fst_strat_conditioned]
      rw [dif_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)]
      rw [dif_pos (by rw [List.getLast_append] ; apply f_act_leg)]
      rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)]
      dsimp
      rw [List.append_nil]
      have := h_f_strat ((Game_World_wDraw.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toGame_World_wDraw
            (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
            (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t ++
             [fst_s g.init_game_state []])) [f_act]
             (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)
             (by apply List.cons_ne_nil)
             (by rw [List.getLast_append] ; apply f_act_leg)
             (by apply f_act_leg)
             (by rw [List.getLast_append] ; dsimp)
      rw [this]
      rw [List.getLast_append]
      rfl



lemma zGame_World_wDraw.conditioned_legal_fst
  [Inhabited β] (g : zGame_World_wDraw α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → (Hl : g.fst_legal g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.fst_legal g.init_game_state [] (fst_s g.init_game_state [])) :
  let f_act := fst_s g.init_game_state []
  Strategy_legal_fst g.init_game_state g.fst_legal fst_s (g.fst_strat_conditioned f_strat)
  ↔ Strategy_legal_snd (g.world_after_fst f_act f_act_leg).init_game_state (g.world_after_fst f_act f_act_leg).snd_legal (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) :=
  by
  intro f_act
  constructor
  · intro leg t ts
    have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
    have hc := careless_singleton _ _ _ _ _ (g.f_legal_careless)
    specialize leg (t+1) (by rw [← Turn_snd_fst_step] ; exact ts)
    unfold Game_World_wDraw.history_on_turn at hh
    rw [hh] at leg
    rw [hc] at leg
    · dsimp [snd_strat_conditioned]
      rw [← g.sym_legal]
      apply leg
    · apply f_act_leg
  · intro leg t tf
    cases' t with t
    · dsimp [History_on_turn]
      apply f_act_leg
    · specialize leg (t) (by rw [Turn_snd_fst_step] ; exact tf)
      have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
      have hc := careless_singleton _ _ _ _ _ (g.f_legal_careless)
      unfold Game_World_wDraw.history_on_turn at hh
      rw [hh, hc]
      · dsimp [snd_strat_conditioned] at leg
        rw [g.sym_legal]
        apply leg
      · apply f_act_leg




lemma zGame_World_wDraw.conditioned_legal_snd
  [Inhabited β] (g : zGame_World_wDraw α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → (Hl : g.fst_legal g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.fst_legal g.init_game_state [] (fst_s g.init_game_state [])) :
  let f_act := fst_s g.init_game_state []
  Strategy_legal_snd g.init_game_state g.snd_legal fst_s (g.fst_strat_conditioned f_strat)
  ↔ Strategy_legal_fst (g.world_after_fst f_act f_act_leg).init_game_state (g.world_after_fst f_act f_act_leg).fst_legal (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) :=
  by
  intro f_act
  constructor
  · intro leg t tf
    have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
    have hc := careless_singleton _ _ _ _ _ (g.s_legal_careless)
    specialize leg (t+1) (by rw [← Turn_fst_snd_step] ; exact tf)
    unfold Game_World_wDraw.history_on_turn at hh
    rw [hh] at leg
    rw [hc] at leg
    · dsimp [snd_strat_conditioned]
      rw [g.sym_legal]
      dsimp [fst_strat_conditioned] at leg
      rw [dif_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)] at leg
      rw [dif_pos (by rw [List.getLast_append] ; apply f_act_leg)] at leg
      rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)] at leg
      dsimp at leg
      rw [List.append_nil] at leg
      have := h_f_strat ((Game_World_wDraw.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toGame_World_wDraw
              (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
              (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t ++
              [fst_s g.init_game_state []])) [f_act]
              (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)
              (by apply List.cons_ne_nil)
              (by rw [List.getLast_append] ; apply f_act_leg)
              (by apply f_act_leg)
              (by rw [List.getLast_append] ; dsimp)
      unfold Game_World_wDraw.history_on_turn at this
      rw [this] at leg
      rw [List.getLast_append] at leg
      apply leg
    · apply f_act_leg
  · intro leg t ts
    cases' t with t
    · contradiction
    · have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
      have hc := careless_singleton _ _ _  _ _ (g.s_legal_careless)
      specialize leg (t) (by rw [Turn_fst_snd_step] ; exact ts)
      unfold Game_World_wDraw.history_on_turn at hh
      rw [hh]
      rw [hc]
      · rw [← g.sym_legal]
        rw [zGame_World_wDraw.world_after_fst_fst_legal] at leg
        convert leg using 1
        dsimp [fst_strat_conditioned]
        rw [dif_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)]
        rw [dif_pos (by rw [List.getLast_append] ; apply f_act_leg)]
        rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)]
        dsimp
        rw [List.append_nil]
        have := h_f_strat ((Game_World_wDraw.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toGame_World_wDraw
                (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
                (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t ++
                [fst_s g.init_game_state []])) [f_act]
                (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)
                (by apply List.cons_ne_nil)
                (by rw [List.getLast_append] ; apply f_act_leg)
                (by apply f_act_leg)
                (by rw [List.getLast_append] ; dsimp)
        unfold Game_World_wDraw.history_on_turn at this
        rw [this]
        rw [List.getLast_append]
        rfl
      · apply f_act_leg



lemma zGame_World_wDraw.conditioned_state_on_turn_neutral
  [Inhabited β] (g : zGame_World_wDraw α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → (Hl : g.fst_legal g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.fst_legal g.init_game_state [] (fst_s g.init_game_state [])):
  let f_act := fst_s g.init_game_state []
  ∀ t : ℕ,
  g.state_on_turn_neutral fst_s (g.fst_strat_conditioned f_strat) (t+1) =
  (g.world_after_fst f_act f_act_leg).state_on_turn_neutral (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) t:=
  by
  intro f_act t
  dsimp [Game_World_wDraw.state_on_turn_neutral]
  rw [g.state_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg]
  congr 1
  by_cases q : Turn_fst t
  · rw [if_pos q]
    rw [Turn_fst_not_step] at q
    rw [if_neg q]
    rw [g.sym_win]
  · rw [if_neg q]
    rw [Turn_fst_not_step, not_not] at q
    rw [if_pos q]
    rw [g.sym_win]





--#exit

-- lemma zGame_World_wDraw.conditioned_legal_fst' [Inhabited β] (f_strat fst_s: Strategy α β) (g : zGame_World_wDraw α β) :
--   let ws := g.fst_strat_conditioned fst_s
--   (f_leg : Strategy_legal_fst g.init_game_state g.fst_legal f_strat ws) →
--   (ws_leg : Strategy_legal_snd g.init_game_state g.fst_legal f_strat ws) →
--   let f_act := f_strat g.init_game_state []
--   let f_act_leg := f_leg 0 (by decide)
--   Strategy_legal_fst (g.world_after_fst f_act f_act_leg).init_game_state (g.world_after_fst f_act f_act_leg).fst_legal f_strat (g.snd_strat_conditioned f_strat f_act) :=
--   by -- replace fst_act wih stuff
--   sorry -- test on Zermelo first

-- -- lemma zGame_World_wDraw.getLast_is_fst [Inhabited β] (g : zGame_World_wDraw α β)
-- --   (f_strat s_strat: Strategy α β)
-- --   (hist : List β) (hh : hist ≠ []) :

lemma History_on_turn_eq_strats_snd
  (g : zGame_World_wDraw α β) (f_strat sSa aSb: Strategy α β)
  (h : ∀ t, Turn_snd (t+1) →  sSa g.init_game_state (History_on_turn g.init_game_state f_strat sSa (t)) =
          sSb g.init_game_state (History_on_turn g.init_game_state f_strat sSb (t))) :
  History_on_turn g.init_game_state f_strat sSa = History_on_turn g.init_game_state f_strat sSb :=
  by
  funext t
  induction' t with t ih
  · dsimp [History_on_turn]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q, if_pos q, ih]
    · specialize h t (by rw [Turn_not_fst_iff_snd] at q ; exact q)
      rw [if_neg q, if_neg q, h, ih]


lemma Strategy_legal_fst_eq_strats_snd
  (g : zGame_World_wDraw α β) (f_strat sSa sSb: Strategy α β)
  (h : ∀ t, Turn_snd (t+1) → sSa g.init_game_state (History_on_turn g.init_game_state f_strat sSa (t)) =
          sSb g.init_game_state (History_on_turn g.init_game_state f_strat sSb (t)))
  (hl : Strategy_legal_fst g.init_game_state g.fst_legal f_strat sSa) :
  Strategy_legal_fst g.init_game_state g.fst_legal f_strat sSb :=
  by
  intro t tf
  rw [← History_on_turn_eq_strats_snd g f_strat sSa sSb h]
  exact hl t tf


lemma Strategy_legal_snd_eq_strats_snd
  (g : zGame_World_wDraw α β) (f_strat sSa sSb: Strategy α β)
  (h : ∀ t, Turn_snd (t+1) → sSa g.init_game_state (History_on_turn g.init_game_state f_strat sSa (t)) =
          sSb g.init_game_state (History_on_turn g.init_game_state f_strat sSb (t)))
  (hl : Strategy_legal_snd g.init_game_state g.snd_legal f_strat sSa) :
  Strategy_legal_snd g.init_game_state g.snd_legal f_strat sSb :=
  by
  intro t ts
  rw [← History_on_turn_eq_strats_snd g f_strat sSa sSb h]
  specialize hl t ts
  rw [h t ts, ← History_on_turn_eq_strats_snd g f_strat sSa sSb h] at hl
  exact hl



lemma Conditioning_win [Inhabited β] (g : zGame_World_wDraw α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.fst_legal g.init_game_state [] (h.getLast hne)) → (Hl : g.fst_legal g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.fst_legal g.init_game_state [] (fst_s g.init_game_state []))
  (Leg_f : Strategy_legal_fst g.init_game_state g.fst_legal fst_s (zGame_World_wDraw.fst_strat_conditioned g f_strat))
  (Leg_s : Strategy_legal_snd g.init_game_state g.snd_legal fst_s (zGame_World_wDraw.fst_strat_conditioned g f_strat))
  (wlg_d : ¬Game_World_wDraw.draw_states g.toGame_World_wDraw g.init_game_state)
  (wlg_ws : ¬Game_World.snd_win_states g.toGame_World g.init_game_state)
  (hw : let f_act := fst_s g.init_game_state []
        Game_wDraw.fst_win { toGame_World_wDraw := (g.world_after_fst f_act f_act_leg).toGame_World_wDraw,
                              fst_strat := f_strat [f_act] (by apply List.cons_ne_nil) f_act_leg,
                              snd_strat := g.snd_strat_conditioned fst_s f_act,
                              fst_lawful :=
                                (by
                                have := g.conditioned_legal_snd fst_s f_strat h_f_strat f_act_leg
                                dsimp at this
                                rw [zGame_World_wDraw.world_after_fst_fst_legal, ← this]
                                exact Leg_s),
                              snd_lawful :=
                                (by
                                have := g.conditioned_legal_fst fst_s f_strat h_f_strat f_act_leg
                                dsimp at this
                                rw [zGame_World_wDraw.world_after_fst_snd_legal, ← this]
                                exact Leg_f),
                                }) :
    Game_wDraw.snd_win { toGame_World_wDraw := g.toGame_World_wDraw,
                          fst_strat := fst_s,
                          snd_strat := (zGame_World_wDraw.fst_strat_conditioned g f_strat),
                          fst_lawful := (Leg_f),
                          snd_lawful := (Leg_s)} :=
  by
  obtain ⟨t, ⟨ts,tw,tn⟩⟩ := hw
  use (t+1)
  constructor
  · rw [← Turn_fst_snd_step]
    exact ts
  · constructor
    · rw [← g.sym_win]
      dsimp at tw
      convert tw using 1
      apply g.state_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg
    · intro n nt
      cases' n with n
      · dsimp [Game_wDraw.state_on_turn_neutral]
        rw [if_neg (by decide)]
        dsimp [Game_wDraw.state_on_turn]
        constructor
        · exact wlg_d
        · exact wlg_ws
      · have := g.conditioned_state_on_turn_neutral fst_s f_strat h_f_strat f_act_leg n
        apply Game_wDraw.state_on_turn_neutral_from_World _ (n+1)
        dsimp
        rw [this]
        apply tn
        exact Nat.lt_of_add_lt_add_right nt
