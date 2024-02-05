/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic



/--
### Games

Games are determined 2 types:
- `α`, the type representing the state of the game
- `β`, the type representing actions

As well as 4 data:

- `init_game_state` : the intitial state of the game
- `transition` : a function taking the current state and current action as input
                 and returning the next state as output. The uniqueness of this
                 transition function assumes that transitions are independent of
                 which player has the turn.
-
-/
structure Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the first player-/
  fst_win_states : α → Prop
  /-- Given the initial state, the history, and an action of the frist player, return next state-/
  fst_transition : List β → β → α
  /-- Given the initial state and the history, return a predicate
  that determines the legal actions for the first player-/
  fst_legal : List β → (β → Prop)
  /-- A predicate that decides in which states the game is won for the second player-/
  snd_win_states : α → Prop
  /-- Given the initial state, the history, and an action of the second player, return next state-/
  snd_transition : List β → β → α
  /-- Given the initial state and the history, return a predicate
  that determines the legal actions for the second player-/
  snd_legal : List β → (β → Prop)


structure Symm_Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the first player-/
  win_states : α → Prop
  /-- Given the initial state, the history, and an action of the frist player, return next state-/
  transition : List β → β → α
  law : List β → (β → Prop)


/--
The list of actions represents the history of actions taken
by both players. From the history and initial state (first input),
one may deduce the current state, which may be used to define
startegies.
-/
abbrev Game.strategy (α β : Type u) := α → List β → β

abbrev Game.strategy_legal {α β : Type u}
  (ini : α) (law : List β → (β → Prop)) (strat : Game.strategy α β): Prop :=
  ∀ hist : List β, law hist (strat ini hist)

structure Game (α β : Type u) extends Game_World α β where
  fst_strat : Game.strategy α β
  fst_lawful :  Game.strategy_legal init_game_state fst_legal fst_strat
  snd_strat : Game.strategy α β
  snd_lawful : Game.strategy_legal init_game_state snd_legal snd_strat


structure Symm_Game (α β : Type u) extends Symm_Game_World α β where
  fst_strat : Game.strategy α β
  fst_lawful :  Game.strategy_legal init_game_state law fst_strat
  snd_strat : Game.strategy α β
  snd_lawful : Game.strategy_legal init_game_state law snd_strat

def Symm_Game.toGame {α β : Type u} (g : Symm_Game α β) : Game α β :=
 {init_game_state := g.init_game_state
  fst_win_states := g.win_states
  fst_transition := g.transition
  fst_legal := g.law
  snd_win_states := g.win_states
  snd_transition := g.transition
  snd_legal := g.law
  fst_strat := g.fst_strat
  fst_lawful := g.fst_lawful
  snd_strat := g.snd_strat
  snd_lawful := g.snd_lawful
  }


-- structure Symm_Game (α β : Type u) extends Game α β where
--   win_symm : fst_win_states = snd_win_states
--   transition_symm : fst_transition = snd_transition
--   legal_symm : fst_legal = snd_legal


-- def Symm_Game.build {α β : Type u}
--  (init : α)
--  (win_states : α → Prop)
--  (transition : List β → β → α)
--  (law : List β → (β → Prop))
--  (f_strat s_strat: Game.strategy α β)
--  (f_lawful :  Game.strategy_legal init law f_strat)
--  (s_lawful :  Game.strategy_legal init law s_strat) :
--  Symm_Game α β where
--   init_game_state := init
--   fst_win_states := win_states
--   fst_transition := transition
--   snd_win_states := win_states
--   snd_transition := transition
--   fst_strat := f_strat
--   snd_strat := s_strat
--   fst_legal := law
--   snd_legal := law
--   fst_lawful := f_lawful
--   snd_lawful := s_lawful
--   win_symm := by rfl
--   transition_symm := by rfl
--   legal_symm := by rfl

-- def Symm_Game.from_world {α β : Type u} (g : Symm_Game_World α β)
--  (f_strat s_strat: Game.strategy α β)
--  (f_lawful :  Game.strategy_legal g.init_game_state g.law f_strat)
--  (s_lawful :  Game.strategy_legal  g.init_game_state g.law s_strat) :
--  Symm_Game α β where
--   init_game_state := g.init_game_state
--   fst_win_states := g.win_states
--   fst_transition := g.transition
--   snd_win_states := g.win_states
--   snd_transition := g.transition
--   fst_strat := f_strat
--   snd_strat := s_strat
--   fst_legal := g.law
--   snd_legal := g.law
--   fst_lawful := f_lawful
--   snd_lawful := s_lawful
--   win_symm := by rfl
--   transition_symm := by rfl
--   legal_symm := by rfl


/-- Turn 0 represents initial state, then turns represent the state after the action-/
def Game.turn_fst (turn : ℕ): Prop := turn % 2 = 1

def Game.turn_snd (turn : ℕ): Prop := ¬ (turn % 2 = 1)

instance : DecidablePred Game.turn_fst :=
  fun turn => by rw [Game.turn_fst] ; exact Nat.decEq (turn % 2) 1

instance : DecidablePred Game.turn_snd :=
  fun turn => by rw [Game.turn_snd] ; exact Not.decidable

lemma Game.turn_not_fst_iff_snd (turn : ℕ) : (¬ Game.turn_fst turn) ↔ Game.turn_snd turn :=
  by rw [Game.turn_fst, Game.turn_snd]

lemma Game.turn_not_snd_iff_fst (turn : ℕ) : (¬ Game.turn_snd turn) ↔ Game.turn_fst turn :=
  by rw [Game.turn_fst, Game.turn_snd, not_ne_iff]

lemma Game.turn_fst_or_snd (turn : ℕ) : Game.turn_fst turn ∨ Game.turn_snd turn :=
  by rw [Game.turn_fst, Game.turn_snd] ; apply em


/-- Computes the history for a given turn, at the end of the turn-/
def Game.history_on_turn {α β : Type u} (g : Game_World α β)
    (fst_strat snd_strat: Game.strategy α β) : ℕ → List β
| 0 => []
| n+1 => let h := Game.history_on_turn g fst_strat snd_strat n
         if Game.turn_fst (n+1)
         then (fst_strat g.init_game_state h) :: h
         else (snd_strat g.init_game_state h) :: h


/-- Computes the history for a given turn-/
def Game.history_on_turn' {α β : Type u} (g : Game α β) : ℕ → List β :=
  Game.history_on_turn g.toGame_World g.fst_strat g.snd_strat


/-- Computes the state for a given turn, after the action was played-/
def Game.state_on_turn {α β : Type u} (g : Game_World α β)
    (fst_strat snd_strat: Game.strategy α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := Game.history_on_turn g fst_strat snd_strat n
         if Game.turn_fst (n+1)
         then g.fst_transition h (fst_strat g.init_game_state h)
         else g.snd_transition h (snd_strat g.init_game_state h)


/-- Computes the state for a given turn-/
def Game.state_on_turn' {α β : Type u} (g : Game α β) : ℕ → α :=
  Game.state_on_turn g.toGame_World g.fst_strat g.snd_strat

def Game.state_on_turn_neutral {α β : Type u} (g : Game α β) (turn : ℕ) : Prop :=
  if Game.turn_fst turn
  then ¬ (g.fst_win_states (g.state_on_turn' turn))
  else ¬ (g.snd_win_states (g.state_on_turn' turn))

-- so one wins by having reach the win state at the end of ones turn
def Game.fst_win  {α β : Type u} (g : Game α β) : Prop :=
  ∃ turn : ℕ, Game.turn_fst turn ∧ g.fst_win_states (g.state_on_turn' turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game.snd_win  {α β : Type u} (g : Game α β) : Prop :=
  ∃ turn : ℕ, Game.turn_snd turn  ∧ g.snd_win_states (g.state_on_turn' turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)


def Game.is_fst_win  {α β : Type u} (g : Game α β) : Prop :=
  ∃ ws : Game.strategy α β, ∃ ws_leg : Game.strategy_legal g.init_game_state g.fst_legal ws,
  ∀ snd_s : Game.strategy α β, (snd_leg : Game.strategy_legal g.init_game_state g.snd_legal snd_s) →
  {g with  fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg}.fst_win

def Game.is_snd_win  {α β : Type u} (g : Game α β) : Prop :=
  ∃ ws : Game.strategy α β, ∃ ws_leg : Game.strategy_legal g.init_game_state g.snd_legal ws,
  ∀ fst_s : Game.strategy α β, (fst_leg : Game.strategy_legal g.init_game_state g.fst_legal fst_s) →
  {g with  fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg}.snd_win


-- so not including input turn itself, to keep with range convention
def Game.state_upto_turn {α β : Type u} (g : Game_World α β)
    (fst_strat snd_strat: Game.strategy α β) (turn : ℕ) : List α :=
  List.map (Game.state_on_turn g fst_strat snd_strat) (List.range turn)


def Game.state_upto_turn' {α β : Type u} (g : Game α β) (turn : ℕ) : List α :=
  List.map g.state_on_turn' (List.range turn)


lemma Game.turn_fst_step (turn : ℕ): Game.turn_fst turn ↔ Game.turn_fst (turn + 2) :=
  by
  constructor
  · intro h
    rw [Game.turn_fst] at *
    rw [Nat.add_mod]
    rw [h]
    decide
  · intro h
    rw [Game.turn_fst] at *
    rw [Nat.add_mod] at h
    norm_num at h
    exact h

lemma Game.turn_snd_step (turn : ℕ): Game.turn_snd turn ↔ Game.turn_snd (turn + 2) :=
  by
  rw [← Game.turn_not_fst_iff_snd, ← Game.turn_not_fst_iff_snd]
  rw [@not_iff_not]
  apply Game.turn_fst_step

lemma Game.turn_fst_snd_step (turn : ℕ): Game.turn_fst turn ↔ Game.turn_snd (turn + 1) :=
  by
  constructor
  · intro h
    rw [Game.turn_fst, Game.turn_snd] at *
    rw [Nat.add_mod]
    rw [h]
    decide
  · intro h
    rw [Game.turn_fst, Game.turn_snd] at *
    have := (or_iff_not_imp_right.mp (Nat.mod_two_eq_zero_or_one (turn+1))) h
    rw [Nat.succ_mod_two_eq_zero_iff] at this
    exact this


lemma Game.turn_snd_fst_step (turn : ℕ): Game.turn_snd turn ↔ Game.turn_fst (turn + 1) :=
  by
  rw [← Game.turn_not_fst_iff_snd, ← @Game.turn_not_snd_iff_fst (turn + 1)]
  rw [@not_iff_not]
  apply Game.turn_fst_snd_step
