/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic



inductive Game_World_wDraw.Turn_isWLD (g : Game_World_wDraw α β) (f_strat s_strat : Strategy α β) (turn : ℕ) : Prop where
| wf : Turn_fst turn → g.fst_win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| ws : Turn_snd turn → g.snd_win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| d : g.draw_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn


def Game_World_wDraw.isWLD (g : Game_World_wDraw α β) : Prop :=
    ∀ f_strat s_strat : Strategy α β,
    (f_leg : Strategy_legal_fst g.init_game_state g.fst_legal f_strat s_strat) →
    (s_leg : Strategy_legal_snd g.init_game_state g.snd_legal f_strat s_strat) →
    ∃ turn, g.Turn_isWLD f_strat s_strat turn


structure Game_World_Terminating (α β : Type u) extends Game_World_wDraw α β where
  termination : toGame_World_wDraw.isWLD


def Game_World_wDraw.isWLD_wBound (g : Game_World_wDraw α β) (T : ℕ) : Prop :=
    ∀ f_strat s_strat : Strategy α β,
    (f_leg : Strategy_legal_fst g.init_game_state g.fst_legal f_strat s_strat) →
    (s_leg : Strategy_legal_snd g.init_game_state g.snd_legal f_strat s_strat) →
    ∃ turn ≤ T, g.Turn_isWLD f_strat s_strat turn


structure Game_World_Finite (α β : Type u) extends Game_World_wDraw α β where
  bound : ℕ
  termination : toGame_World_wDraw.isWLD_wBound bound



/--
Given a game world and strategies, the state on a turn is "neutral"
if it doesn't satifiy the winning state conditions of the player with
the corresponding turn.
-/
def Game_World.state_on_turn_neutral {α β : Type u} (g : Game_World α β)
  (f_strat s_strat : Strategy α β) (turn : ℕ) : Prop :=
  if Turn_fst turn
  then ¬ (g.fst_win_states (g.state_on_turn f_strat s_strat turn))
  else ¬ (g.snd_win_states (g.state_on_turn f_strat s_strat turn))


/--
ADD DOC
-/
def Game_World_wDraw.state_on_turn_neutral {α β : Type u} (g : Game_World_wDraw α β)
  (f_strat s_strat : Strategy α β) (turn : ℕ) : Prop :=
  (¬ g.draw_states (g.state_on_turn f_strat s_strat turn))
  ∧
  (if Turn_fst turn
  then ¬ (g.fst_win_states (g.state_on_turn f_strat s_strat turn))
  else ¬ (g.snd_win_states (g.state_on_turn f_strat s_strat turn)))



/--
Given a symmetric game world and strategies, the state on a turn is "neutral"
if it doesn't satifiy the winning state conditions of the player with
the corresponding turn.
-/
def Symm_Game_World.state_on_turn_neutral {α β : Type u} (g : Symm_Game_World α β)
  (f_strat s_strat : Strategy α β) (turn : ℕ) : Prop :=
  if Turn_fst turn
  then ¬ (g.win_states (g.state_on_turn f_strat s_strat turn))
  else ¬ (g.win_states (g.state_on_turn f_strat s_strat turn))

/--
Given a game, the state on a turn is "neutral"
if it doesn't satifiy the winning state conditions of the player with
the corresponding turn.
-/
def Game.state_on_turn_neutral {α β : Type u} (g : Game α β) (turn : ℕ) : Prop :=
  if Turn_fst turn
  then ¬ (g.fst_win_states (g.state_on_turn turn))
  else ¬ (g.snd_win_states (g.state_on_turn turn))

/--
Given a game, the state on a turn is "neutral"
if it doesn't satifiy the winning state conditions of the player with
the corresponding turn.
-/
def Symm_Game.state_on_turn_neutral {α β : Type u} (g : Symm_Game α β) (turn : ℕ) : Prop :=
  if Turn_fst turn
  then ¬ (g.win_states (g.state_on_turn turn))
  else ¬ (g.win_states (g.state_on_turn turn))


/--
ADD DOC
-/
def Game_wDraw.state_on_turn_neutral {α β : Type u} (g : Game_wDraw α β) (turn : ℕ) : Prop :=
  (¬ g.draw_states (g.state_on_turn turn))
  ∧
  (if Turn_fst turn
  then ¬ (g.fst_win_states (g.state_on_turn turn))
  else ¬ (g.snd_win_states (g.state_on_turn turn)))


@[simp]
lemma Symm_Game.state_on_turn_neutral_toWorld {α β : Type u} (g : Symm_Game α β) :
  g.toSymm_Game_World.state_on_turn_neutral g.fst_strat g.snd_strat = g.state_on_turn_neutral := by rfl

@[simp]
lemma Game.state_on_turn_neutral_toWorld {α β : Type u} (g : Game α β) :
  g.toGame_World.state_on_turn_neutral g.fst_strat g.snd_strat = g.state_on_turn_neutral := by rfl

@[simp]
lemma Symm_Game.state_on_turn_neutral_toGame {α β : Type u} (g : Symm_Game α β) :
  g.toGame.state_on_turn_neutral = g.state_on_turn_neutral := by rfl

@[simp]
lemma Symm_Game_World.state_on_turn_neutral_toWorld {α β : Type u} (g : Symm_Game_World α β):
  g.toGame_World.state_on_turn_neutral = g.state_on_turn_neutral := by rfl




-- # Termination


/--
A game is won by the first player if there exists a turn that is the first
players turn, in which the winning condition for the first player is achieved
by the current state, and for which all prior turn had neutral states.
So one wins by having reached the win state at the end of ones turn.
-/
def Game.fst_win  {α β : Type u} (g : Game α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn ∧ g.fst_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

/--
A game is won by the second player if there exists a turn that is the second
players turn, in which the winning condition for the second player is achieved
by the current state, and for which all prior turn had neutral states.
So one wins by having reached the win state at the end of ones turn.
-/
def Game.snd_win  {α β : Type u} (g : Game α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.snd_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)


def Game_wDraw.fst_draw {α β : Type u} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn  ∧ g.draw_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)


def Game_wDraw.snd_draw {α β : Type u} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.draw_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)


def Game_wDraw.draw {α β : Type u} (g : Game_wDraw α β) : Prop :=
  g.fst_draw ∨ g.snd_draw


/--
A game world allows for a winning stategy for the first player, if there exists
a stategy for which, for any other stategy, such that both are legal wrt. the
laws of the game world and each other, the game in which these startegies are
played is won by the first player.
-/
def Game_World.is_fst_win  {α β : Type u} (g : Game_World α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ snd_s : Strategy α β,
   (ws_leg : Strategy_legal_fst g.init_game_state g.fst_legal ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state g.snd_legal ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Game α β).fst_win

/--
A game world allows for a winning stategy for the second player, if there exists
a stategy for which, for any other stategy, such that both are legal wrt. the
laws of the game world and each other, the game in which these startegies are
played is won by the second player.
-/
def Game_World.is_snd_win  {α β : Type u} (g : Game_World α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   (ws_leg : Strategy_legal_snd g.init_game_state g.snd_legal fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state g.fst_legal fst_s ws) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Game α β).snd_win


def Symm_Game.fst_win  {α β : Type u} (g : Symm_Game α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn ∧ g.win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Symm_Game.snd_win  {α β : Type u} (g : Symm_Game α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)


def Symm_Game_World.is_fst_win  {α β : Type u} (g : Symm_Game_World α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ snd_s : Strategy α β,
   (ws_leg : Strategy_legal_fst g.init_game_state g.law ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state g.law ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Symm_Game α β).fst_win


def Symm_Game_World.is_snd_win  {α β : Type u} (g : Symm_Game_World α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   (ws_leg : Strategy_legal_snd g.init_game_state g.law fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state g.law fst_s ws ) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Symm_Game α β).snd_win




def Game_wDraw.fst_win  {α β : Type u} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn ∧ g.fst_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

/--
A game is won by the second player if there exists a turn that is the second
players turn, in which the winning condition for the second player is achieved
by the current state, and for which all prior turn had neutral states.
So one wins by having reached the win state at the end of ones turn.
-/
def Game_wDraw.snd_win  {α β : Type u} (g : Game_wDraw α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.snd_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

/--
A game world allows for a winning stategy for the first player, if there exists
a stategy for which, for any other stategy, such that both are legal wrt. the
laws of the game world and each other, the game in which these startegies are
played is won by the first player.
-/
def Game_World_wDraw.is_fst_win  {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ snd_s : Strategy α β,
   (ws_leg : Strategy_legal_fst g.init_game_state g.fst_legal ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state g.snd_legal ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Game α β).fst_win

/--
A game world allows for a winning stategy for the second player, if there exists
a stategy for which, for any other stategy, such that both are legal wrt. the
laws of the game world and each other, the game in which these startegies are
played is won by the second player.
-/
def Game_World_wDraw.is_snd_win  {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   (ws_leg : Strategy_legal_snd g.init_game_state g.snd_legal fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state g.fst_legal fst_s ws) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Game α β).snd_win


def Game_World_wDraw.is_fst_draw  {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ snd_s : Strategy α β,
   (ws_leg : Strategy_legal_fst g.init_game_state g.fst_legal ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state g.snd_legal ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Game_wDraw α β).fst_draw


def Game_World_wDraw.is_snd_draw  {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   (ws_leg : Strategy_legal_snd g.init_game_state g.snd_legal fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state g.fst_legal fst_s ws) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Game_wDraw α β).snd_draw

def Game_World_wDraw.is_draw {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  g.is_fst_draw ∨ g.is_snd_draw


@[simp]
lemma Symm_Game.fst_win_toGame  {α β : Type u} (g : Symm_Game α β) :
  g.toGame.fst_win ↔ g.fst_win := by rfl

@[simp]
lemma Symm_Game.snd_win_toGame  {α β : Type u} (g : Symm_Game α β) :
  g.toGame.snd_win ↔ g.snd_win := by rfl

@[simp]
lemma Symm_Game_World.is_fst_win_toGame  {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.is_fst_win ↔ g.is_fst_win := by rfl

@[simp]
lemma Symm_Game_World.snd_win_toGame  {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.is_snd_win ↔ g.is_snd_win := by rfl



inductive Game_World_wDraw.has_WLD (g : Game_World_wDraw α β) : Prop where
| wf : g.is_fst_win → g.has_WLD
| ws : g.is_snd_win → g.has_WLD
| d : g.is_draw → g.has_WLD
