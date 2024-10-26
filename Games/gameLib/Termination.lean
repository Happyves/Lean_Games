/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic




/-
This file defines notions surrounding those of termination of games and winng strategies.
The big picture is:
- `Turn_isWL` defines what it means for a turn to be terminal
- `isWL` defines what it means for a `Game_World` having all its possible games terminate
- `fst_win` and `snd_win` define what it means for a game to be won by the corresponding player
- `is_fst_win` and `is_snd_win` define what it means for either player to have a winning strategy.

-/


/--
A turn is win or lose (WL) if the `hist_on_turn` at that turn satisfies
one of the predicates that decide if a player wins at that stage in the game.
-/
inductive Game_World.Turn_isWL (g : Game_World α β)

  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop where
  | wf : g.fst_win_states (g.hist_on_turn f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn
  | ws : g.snd_win_states  (g.hist_on_turn f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.Turn_isWL (g : Symm_Game_World α β)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  Game_World.Turn_isWL (g.toGame_World) f_strat s_strat turn

/--
A `Game_World` is win or lose (WL) if for any pair of strategies the players
can play it with, there will come a turn that is win or lose when playing by
these strategies.

In particular, all games terminate.
-/
def Game_World.isWL (g : Game_World α β)
  : Prop :=
  ∀ (f_strat : g.fStrategy), ∀ (s_strat : g.sStrategy),
  ∃ turn, g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.isWL (g : Symm_Game_World α β)
  : Prop :=
  ∀ (f_strat : g.fStrategy), ∀ (s_strat : g.sStrategy),
  ∃ turn, g.Turn_isWL f_strat s_strat turn


def Game_World.state_on_turn_neutral (g : Game_World α β)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  ¬ g.Turn_isWL f_strat s_strat turn

def Symm_Game_World.state_on_turn_neutral (g : Symm_Game_World α β)

  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  Game_World.state_on_turn_neutral (g.toGame_World) f_strat s_strat turn

def Game.state_on_turn_neutral (g : Game α β)

  (turn : ℕ) : Prop :=
  g.toGame_World.state_on_turn_neutral g.fst_strat g.snd_strat turn

def Symm_Game.state_on_turn_neutral (g : Symm_Game α β)
  (turn : ℕ) : Prop :=
  Game.state_on_turn_neutral g.toGame turn

/-- The game is won by the first player if there is a turn such that
all prior turns were neutral, and the first winning predicate is satisfied
at that turn

In particular, the game terminates.
-/
def Game.fst_win (g : Game α β)
   : Prop :=
  ∃ turn : ℕ, g.fst_win_states (g.hist_on_turn turn) ∧ (∀ t < turn, g.state_on_turn_neutral t)

/-- The game is won by the second player if there is a turn such that
all prior turns were neutral, and the second winning predicate is satisfied
at that turn

In particular, the game terminates.
-/
def Game.snd_win (g : Game α β)
   : Prop :=
  ∃ turn : ℕ, g.snd_win_states (g.hist_on_turn turn) ∧ (∀ t < turn, g.state_on_turn_neutral t)

def Symm_Game.fst_win (g : Symm_Game α β)
  : Prop :=
  Game.fst_win g.toGame

def Symm_Game.snd_win (g : Symm_Game α β)
   : Prop :=
  Game.snd_win g.toGame


/--
A `Game_World` has a winning strategy for the frist player, if for all strategies
available to the second player, the games played with these strategies are always
won by the first player.

In particular, all games terminate.
-/
def Game_World.is_fst_win (g : Game_World α β)
   : Prop :=
  ∃ ws : g.fStrategy, ∀ snd_s : g.sStrategy,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game α β).fst_win


/--
A `Game_World` has a winning strategy for the second player, if for all strategies
available to the first player, the games played with these strategies are always
won by the second player.

In particular, all games terminate.
-/
def Game_World.is_snd_win (g : Game_World α β)
   : Prop :=
  ∃ ws : g.sStrategy, ∀ snd_s : g.fStrategy,
  ({g with snd_strat := ws, fst_strat := snd_s} : Game α β).snd_win

def Symm_Game_World.is_fst_win (g : Symm_Game_World α β)
   : Prop :=
  Game_World.is_fst_win g.toGame_World

def Symm_Game_World.is_snd_win (g : Symm_Game_World α β)
  : Prop :=
  Game_World.is_snd_win g.toGame_World

/--
The `Game_World` has a winning strategy if it has one for one of the players.
-/
inductive Game_World.has_WL (g : Game_World α β)
   : Prop where
  | wf (h : g.is_fst_win)
  | ws (h : g.is_snd_win)

def Symm_Game_World.has_WL (g : Symm_Game_World α β) :=
  Game_World.has_WL g.toGame_World


lemma Game_World.state_on_turn_neutral_State_from_history_neutral (g : Game_World α β)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) :
  g.state_on_turn_neutral f_strat s_strat turn ↔
  g.hist_neutral (g.hist_on_turn f_strat s_strat turn).val :=
  by
  dsimp [Game_World.state_on_turn_neutral]
  constructor
  · intro h
    constructor
    · contrapose! h ; apply Game_World.Turn_isWL.wf h
    · contrapose! h ; apply Game_World.Turn_isWL.ws h
  · intro h con
    cases' con with F S
    · exact h.not_fst F
    · exact h.not_snd S


-- # With draw


inductive Game_World_wDraw.Turn_isWLD (g : Game_World_wDraw α β)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop where
| wf : g.fst_win_states (g.hist_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| ws : g.snd_win_states (g.hist_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| drw : g.draw_states (g.hist_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn


def Game_World_wDraw.isWLD (g : Game_World_wDraw α β)
   : Prop :=
  ∀ (f_strat : g.fStrategy), ∀ (s_strat : g.sStrategy),
  ∃ turn, g.Turn_isWLD f_strat s_strat turn


def Game_World_wDraw.state_on_turn_neutral (g : Game_World_wDraw α β)
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) : Prop :=
  ¬ g.Turn_isWLD f_strat s_strat turn


def Game_wDraw.state_on_turn_neutral (g : Game_wDraw α β)
   (turn : ℕ) : Prop :=
  g.toGame_World_wDraw.state_on_turn_neutral g.fst_strat g.snd_strat turn


def Game_wDraw.fst_win  {α β : Type _} (g : Game_wDraw α β)
   : Prop :=
  ∃ turn : ℕ, g.fst_win_states (g.hist_on_turn g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game_wDraw.snd_win  {α β : Type _} (g : Game_wDraw α β)
   : Prop :=
  ∃ turn : ℕ, g.snd_win_states (g.hist_on_turn g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game_wDraw.draw  {α β : Type _} (g : Game_wDraw α β)
   : Prop :=
  ∃ turn : ℕ, g.draw_states (g.hist_on_turn g.fst_strat g.snd_strat turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)


def Game_World_wDraw.is_fst_win  {α β : Type _} (g : Game_World_wDraw α β)
   : Prop :=
  ∃ ws : g.fStrategy, ∀ snd_s : g.sStrategy,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw α β).fst_win

def Game_World_wDraw.is_snd_win  {α β : Type _} (g : Game_World_wDraw α β)
   : Prop :=
  ∃ ws : g.sStrategy, ∀ snd_s : g.fStrategy,
  ({g with snd_strat := ws, fst_strat := snd_s} : Game_wDraw α β).fst_win

def Game_World_wDraw.is_draw_fst  {α β : Type _} (g : Game_World_wDraw α β)
   : Prop :=
  ∃ ws : g.fStrategy, ∀ snd_s : g.sStrategy,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw α β).draw

def Game_World_wDraw.is_draw_snd  {α β : Type _} (g : Game_World_wDraw α β)
   : Prop :=
  ∃ ws : g.sStrategy, ∀ snd_s : g.fStrategy,
  ({g with snd_strat := ws, fst_strat := snd_s} : Game_wDraw α β).draw

def Game_World_wDraw.is_draw {α β : Type _} (g : Game_World_wDraw α β)
  : Prop :=
  g.is_draw_fst ∨ g.is_draw_snd

inductive Game_World_wDraw.has_WLD (g : Game_World_wDraw α β)
   : Prop where
  | wf (h : g.is_fst_win)
  | ws (h : g.is_snd_win)
  | draw (h : g.is_draw)


lemma Game_World_wDraw.state_on_turn_neutral_hist_neutral (g : Game_World_wDraw α β)

  (f_strat : g.fStrategy) (s_strat : g.sStrategy) (turn : ℕ) :
  g.state_on_turn_neutral f_strat s_strat turn ↔
  g.hist_neutral (g.hist_on_turn f_strat s_strat turn).val :=
  by
  dsimp [Game_World_wDraw.state_on_turn_neutral]
  constructor
  · intro h
    constructor
    · constructor
      · contrapose! h ; apply Game_World_wDraw.Turn_isWLD.wf h
      · contrapose! h ; apply Game_World_wDraw.Turn_isWLD.ws h
    · contrapose! h ; apply Game_World_wDraw.Turn_isWLD.drw h
  · intro h con
    cases' con with F S D
    · exact h.not_fst F
    · exact h.not_snd S
    · exact h.not_draw D


def Game_World_wDraw.is_draw_at_worst_fst {α β : Type _} (g : Game_World_wDraw α β)
   : Prop :=
  ∃ ws : g.fStrategy, ∀ snd_s : g.sStrategy,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw α β).fst_win ∨
  ({g with fst_strat := ws, snd_strat := snd_s} : Game_wDraw  α β).draw

def Game_World_wDraw.is_draw_at_worst_snd {α β : Type _} (g : Game_World_wDraw α β)
   : Prop :=
  ∃ ws : g.sStrategy, ∀ fst_s : g.fStrategy,
  ({g with fst_strat := fst_s, snd_strat := ws} : Game_wDraw α β).snd_win ∨
  ({g with fst_strat := fst_s, snd_strat := ws} : Game_wDraw  α β).draw
