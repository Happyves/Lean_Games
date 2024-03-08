/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic
import Games.exLib.Nat


-- # Environments

/--
The game world for state type α and action type β.
-/
structure Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the first player-/
  fst_win_states : α → Prop
  /-- Given the history, and an action of the frist player, return next state-/
  fst_transition : List β → β → α
  /-- Given the history, return a predicate
  that determines the legal actions for the first player-/
  fst_legal : List β → (β → Prop)
  /-- A predicate that decides in which states the game is won for the second player-/
  snd_win_states : α → Prop
  /-- Given the history, and an action of the second player, return next state-/
  snd_transition : List β → β → α
  /-- Given the history, return a predicate
  that determines the legal actions for the second player-/
  snd_legal : List β → (β → Prop)


structure Game_World_wDraw (α β : Type u) extends Game_World α β where
  draw_states : α → Prop


/--
The game world for state type α and action type β, where players aren't discerened.
-/
structure Symm_Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the players-/
  win_states : α → Prop
  /-- Given  the history, and an action of the player, return next state-/
  transition : List β → β → α
  /-- A predicate that decides in which states the game is won for the players-/
  law : List β → (β → Prop)


/--
Produce a `Game_World` from a `Symm_Game_World`.
-/
def Symm_Game_World.toGame_World {α β : Type u} (g : Symm_Game_World α β) : Game_World α β :=
  {init_game_state := g.init_game_state
   fst_win_states := g.win_states
   fst_transition := g.transition
   fst_legal := g.law
   snd_win_states := g.win_states
   snd_transition := g.transition
   snd_legal := g.law
   }


instance {α β : Type u} : Coe (Symm_Game_World α β) (Game_World α β) where
  coe := Symm_Game_World.toGame_World

@[simp]
lemma Symm_Game_World.toGame_World_ini {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.init_game_state = g.init_game_state :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_fst_win {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.fst_win_states = g.win_states :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_win {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.snd_win_states = g.win_states :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_fst_trans {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.fst_transition = g.transition :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_trans {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.snd_transition = g.transition :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_fst_legal {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.fst_legal = g.law :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_legal {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.snd_legal = g.law :=
  by
  rfl

/--
The list of actions represents the history of actions taken
by both players. From the history and initial state (first input),
one may deduce the current state, which may be used to define
startegies. The output is the action to be played.
-/
abbrev Strategy (α β : Type u) := α → List β → β



/--
Turn of the first player.
Turn 0 represents initial state, then turns represent the state after the action-/
def Turn_fst (turn : ℕ): Prop := turn % 2 = 1

/--
Turn of the decond player.
Turn 0 represents initial state, then turns represent the state after the action-/
def Turn_snd (turn : ℕ): Prop := ¬ (turn % 2 = 1)

instance : DecidablePred Turn_fst :=
  fun turn => by rw [Turn_fst] ; exact Nat.decEq (turn % 2) 1

instance : DecidablePred Turn_snd :=
  fun turn => by rw [Turn_snd] ; exact Not.decidable

/-- The turn given the history-/
abbrev Turn_from_hist {β : Type u} (hist : List β) := hist.length

/-- The history of actions, given an initial state and the two startegies-/
def History_on_turn {α β : Type u}
    (ini : α) (fst_strat snd_strat: Strategy α β) : ℕ → List β
| 0 => []
| n+1 => let h := History_on_turn ini fst_strat snd_strat n
         if Turn_fst (n+1)
         then (fst_strat ini h) :: h
         else (snd_strat ini h) :: h

/--
FIX ME

Given a law that returns a predicate on actions to determine legal actions,
when provided an initial state and a history of actions on which the law may
depend on, we define the notion of a strategy being legal (given another startegy).
A strategy is legal if for all turns, the action for the history on that turn
is legal wrt. the law at that history.
-/
def Strategy_legal_fst {α β : Type u}
  (ini : α) (f_law : α → List β → (β → Prop)) (f_strat s_strat : Strategy α β): Prop :=
  ∀ turn : ℕ, Turn_fst (turn + 1) → f_law ini (History_on_turn ini f_strat s_strat turn) (f_strat ini (History_on_turn ini f_strat s_strat turn))
      -- recall : turn is after the action

/--
FIX ME
-/
def Strategy_legal_snd {α β : Type u}
  (ini : α) (s_law : α → List β → (β → Prop)) (f_strat s_strat : Strategy α β): Prop :=
  ∀ turn : ℕ, Turn_snd (turn +1) → s_law ini (History_on_turn ini f_strat s_strat turn) (s_strat ini (History_on_turn ini f_strat s_strat turn))
      -- recall : turn is after the action


/--
A game is a game world extended by two specific strategies,
and the certificates that they're legal wrt. the laws provided
by the game world.
-/
structure Game (α β : Type u) extends Game_World α β where
  /-- The first players strategy-/
  fst_strat : Strategy α β
  /-- The second players strategy-/
  snd_strat : Strategy α β
  /-- The first players strategy is legal wrt. `fst_legal` and the second strategy-/
  fst_lawful : Strategy_legal_fst init_game_state (fun _ => fst_legal) fst_strat snd_strat
  /-- The second players strategy is legal wrt. `snd_legal` and the first strategy-/
  snd_lawful : Strategy_legal_snd init_game_state (fun _ => snd_legal) fst_strat snd_strat

/-- Same as `Game`, but for a symmetric game world-/
structure Symm_Game (α β : Type u) extends Symm_Game_World α β where
  /-- The first players strategy-/
  fst_strat : Strategy α β
  /-- The second players strategy-/
  snd_strat : Strategy α β
  /-- The first players strategy is legal wrt. `law` and the second strategy-/
  fst_lawful : Strategy_legal_fst init_game_state (fun _ => law) fst_strat snd_strat
  /-- The second players strategy is legal wrt. `law` and the first strategy-/
  snd_lawful : Strategy_legal_snd init_game_state (fun _ => law) fst_strat snd_strat


/-- Build a `Game` from a `Symm_Game`-/
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

/-- ADD DOCS-/
structure Game_wDraw (α β : Type u) extends Game_World_wDraw α β where
  /-- The first players strategy-/
  fst_strat : Strategy α β
  /-- The second players strategy-/
  snd_strat : Strategy α β
  /-- The first players strategy is legal wrt. `fst_legal` and the second strategy-/
  fst_lawful : Strategy_legal_fst init_game_state (fun _ => fst_legal) fst_strat snd_strat
  /-- The second players strategy is legal wrt. `snd_legal` and the first strategy-/
  snd_lawful : Strategy_legal_snd init_game_state (fun _ => snd_legal) fst_strat snd_strat



@[simp]
lemma Symm_Game.toGame_ini {α β : Type u} (g : Symm_Game α β) :
  g.toGame.init_game_state = g.init_game_state :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_fst_win {α β : Type u} (g : Symm_Game α β) :
  g.toGame.fst_win_states = g.win_states :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_snd_win {α β : Type u} (g : Symm_Game α β) :
  g.toGame.snd_win_states = g.win_states :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_fst_trans {α β : Type u} (g : Symm_Game α β) :
  g.toGame.fst_transition = g.transition :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_snd_trans {α β : Type u} (g : Symm_Game α β) :
  g.toGame.snd_transition = g.transition :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_fst_legal {α β : Type u} (g : Symm_Game α β) :
  g.toGame.fst_legal = g.law :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_snd_legal {α β : Type u} (g : Symm_Game α β) :
  g.toGame.snd_legal = g.law :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_fst_strat {α β : Type u} (g : Symm_Game α β) :
  g.toGame.fst_strat = g.fst_strat :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_snd_start {α β : Type u} (g : Symm_Game α β) :
  g.toGame.snd_strat = g.snd_strat :=
  by
  rfl

instance {α β : Type u} : Coe (Symm_Game α β) (Game α β) where
  coe := Symm_Game.toGame


@[simp]
lemma Symm_Game.toSymm_Game_World_ini {α β : Type u} (g : Symm_Game α β) :
  g.toSymm_Game_World.init_game_state = g.init_game_state :=
  by
  rfl



@[simp]
lemma Symm_Game.toGame_toWorld {α β : Type u} (g : Symm_Game α β):
  g.toGame.toGame_World = g.toSymm_Game_World.toGame_World :=
  by
  dsimp [Symm_Game.toGame, Game.toGame_World, Symm_Game.toSymm_Game_World, Symm_Game_World.toGame_World]



/-- History for a given turn, given a game world and stategies-/
def Game_World.history_on_turn {α β : Type u} (g : Game_World α β)
    (fst_strat snd_strat: Strategy α β) : ℕ → List β :=
    History_on_turn g.init_game_state fst_strat snd_strat

lemma Game_World.history_on_turn_def {α β : Type u} (g : Game_World α β) :
    g.history_on_turn = History_on_turn g.init_game_state :=
    by
    rfl

/-- History for a given turn, given a symmetric game world and stategies-/
def Symm_Game_World.history_on_turn {α β : Type u} (g : Symm_Game_World α β)
    (fst_strat snd_strat: Strategy α β) : ℕ → List β :=
    History_on_turn g.init_game_state fst_strat snd_strat

lemma Symm_Game_World.history_on_turn_def {α β : Type u} (g : Symm_Game_World α β):
    g.history_on_turn = History_on_turn g.init_game_state :=
    by
    rfl


/-- History for a given turn, given a game world and stategies-/
def Game_World_wDraw.history_on_turn {α β : Type u} (g : Game_World_wDraw α β)
    (fst_strat snd_strat: Strategy α β) : ℕ → List β :=
    History_on_turn g.init_game_state fst_strat snd_strat

lemma Game_World_wDraw.history_on_turn_def {α β : Type u} (g : Game_World_wDraw α β) :
    g.history_on_turn = History_on_turn g.init_game_state :=
    by
    rfl

@[simp]
lemma History_on_turn_World_symm (g : Symm_Game_World α β):
  g.toGame_World.history_on_turn = g.history_on_turn :=
  by
  funext f_st s_st
  dsimp [Symm_Game_World.history_on_turn, Game_World.history_on_turn, Symm_Game_World.toGame_World]


/-- Computes the history for a given turn, given a game-/
def Game.history_on_turn {α β : Type u} (g : Game α β) : ℕ → List β :=
  History_on_turn g.init_game_state g.fst_strat g.snd_strat

lemma Game.history_on_turn_def {α β : Type u} (g : Game α β) :
  g.history_on_turn = History_on_turn g.init_game_state g.fst_strat g.snd_strat :=
  by
  rfl

/-- Computes the history for a given turn, given a symmetric game-/
def Symm_Game.history_on_turn {α β : Type u} (g : Symm_Game α β) : ℕ → List β :=
  History_on_turn g.init_game_state g.fst_strat g.snd_strat


lemma Symm_Game.history_on_turn_def {α β : Type u} (g : Symm_Game α β) :
  g.history_on_turn = History_on_turn g.init_game_state g.fst_strat g.snd_strat :=
  by
  rfl

/-- Computes the history for a given turn, given a game-/
def Game_wDraw.history_on_turn {α β : Type u} (g : Game_wDraw α β) : ℕ → List β :=
  History_on_turn g.init_game_state g.fst_strat g.snd_strat

lemma Game_wDraw.history_on_turn_def {α β : Type u} (g : Game_wDraw α β) :
  g.history_on_turn = History_on_turn g.init_game_state g.fst_strat g.snd_strat :=
  by
  rfl

@[simp]
lemma History_on_turn_symm (g : Symm_Game α β):
  g.toGame.history_on_turn = g.history_on_turn :=
  by
  dsimp [Symm_Game.history_on_turn, Game.history_on_turn, Symm_Game.toGame]

@[simp]
lemma History_on_turn_toWorld (g : Game α β):
  g.toGame_World.history_on_turn g.fst_strat g.snd_strat = g.history_on_turn :=
  by
  dsimp [Game.history_on_turn, Game_World.history_on_turn, Game.toGame_World]

@[simp]
lemma History_on_turn_symm_toWorld (g : Symm_Game α β):
  g.toSymm_Game_World.history_on_turn g.fst_strat g.snd_strat = g.history_on_turn :=
  by
  dsimp [Symm_Game.history_on_turn, Symm_Game_World.history_on_turn, Symm_Game.toSymm_Game_World]




-- # Turns



lemma Turn_not_fst_iff_snd (turn : ℕ) : (¬ Turn_fst turn) ↔ Turn_snd turn :=
  by rw [Turn_fst, Turn_snd]

lemma Turn_not_snd_iff_fst (turn : ℕ) : (¬ Turn_snd turn) ↔ Turn_fst turn :=
  by rw [Turn_fst, Turn_snd, not_ne_iff]

lemma Turn_fst_or_snd (turn : ℕ) : Turn_fst turn ∨ Turn_snd turn :=
  by rw [Turn_fst, Turn_snd] ; apply em


lemma Turn_fst_step (turn : ℕ): Turn_fst turn ↔ Turn_fst (turn + 2) :=
  by
  constructor
  · intro h
    rw [Turn_fst] at *
    rw [Nat.add_mod]
    rw [h]
    decide
  · intro h
    rw [Turn_fst] at *
    rw [Nat.add_mod] at h
    norm_num at h
    exact h

lemma Turn_snd_step (turn : ℕ): Turn_snd turn ↔ Turn_snd (turn + 2) :=
  by
  rw [← Turn_not_fst_iff_snd, ← Turn_not_fst_iff_snd]
  rw [@not_iff_not]
  apply Turn_fst_step

lemma Turn_fst_snd_step (turn : ℕ): Turn_fst turn ↔ Turn_snd (turn + 1) :=
  by
  constructor
  · intro h
    rw [Turn_fst, Turn_snd] at *
    rw [Nat.add_mod]
    rw [h]
    decide
  · intro h
    rw [Turn_fst, Turn_snd] at *
    have := (or_iff_not_imp_right.mp (Nat.mod_two_eq_zero_or_one (turn+1))) h
    rw [Nat.succ_mod_two_eq_zero_iff] at this
    exact this


lemma Turn_snd_fst_step (turn : ℕ): Turn_snd turn ↔ Turn_fst (turn + 1) :=
  by
  rw [← Turn_not_fst_iff_snd, ← @Turn_not_snd_iff_fst (turn + 1)]
  rw [@not_iff_not]
  apply Turn_fst_snd_step


lemma Turn_fst_not_step (turn : ℕ): Turn_fst turn ↔ ¬ Turn_fst (turn + 1) :=
  by
  rw [Turn_not_fst_iff_snd]
  apply Turn_fst_snd_step


lemma Turn_snd_not_step (turn : ℕ): Turn_snd turn ↔ ¬ Turn_snd (turn + 1) :=
  by
  rw [Turn_not_snd_iff_fst]
  apply Turn_snd_fst_step


lemma History_on_turn_fst_to_snd (ini : α) (fst_strat snd_strat: Strategy α β) (turn : ℕ):
  let H := History_on_turn ini fst_strat snd_strat ;
  Turn_fst turn → H (turn + 1) = (snd_strat ini (H turn)) :: (H turn) :=
  by
  intro H tf
  dsimp [H, History_on_turn]
  rw [if_neg ((Turn_fst_not_step turn).mp tf)]

lemma History_on_turn_snd_to_fst (ini : α) (fst_strat snd_strat: Strategy α β) (turn : ℕ):
  let H := History_on_turn ini fst_strat snd_strat ;
  Turn_snd turn → H (turn + 1) = (fst_strat ini (H turn)) :: (H turn) :=
  by
  intro H tf
  dsimp [H, History_on_turn]
  rw [if_pos ((Turn_snd_fst_step turn).mp tf)]

lemma Symm_Game_World.history_on_turn_fst_to_snd
  {α β : Type u} (g : Symm_Game_World α β)
  (fst_strat snd_strat: Strategy α β) (turn : ℕ):
  let H := g.history_on_turn fst_strat snd_strat ;
  Turn_fst turn → H (turn + 1) = (snd_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game_World.history_on_turn]
  apply History_on_turn_fst_to_snd

lemma Symm_Game_World.history_on_turn_snd_to_fst
  {α β : Type u} (g : Symm_Game_World α β)
  (fst_strat snd_strat: Strategy α β) (turn : ℕ):
  let H := g.history_on_turn fst_strat snd_strat ;
  Turn_snd turn → H (turn + 1) = (fst_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game_World.history_on_turn]
  apply History_on_turn_snd_to_fst


lemma Game_World.history_on_turn_fst_to_snd
  {α β : Type u} (g : Game_World α β)
  (fst_strat snd_strat: Strategy α β) (turn : ℕ):
  let H := g.history_on_turn fst_strat snd_strat ;
  Turn_fst turn → H (turn + 1) = (snd_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Game_World.history_on_turn]
  apply History_on_turn_fst_to_snd

lemma Game_World.history_on_turn_snd_to_fst
  {α β : Type u} (g : Game_World α β)
  (fst_strat snd_strat: Strategy α β) (turn : ℕ):
  let H := g.history_on_turn fst_strat snd_strat ;
  Turn_snd turn → H (turn + 1) = (fst_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Game_World.history_on_turn]
  apply History_on_turn_snd_to_fst


lemma Game.history_on_turn_fst_to_snd
  {α β : Type u} (g : Game α β) (turn : ℕ):
  let H := g.history_on_turn ;
  Turn_fst turn → H (turn + 1) = (g.snd_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Game.history_on_turn]
  apply History_on_turn_fst_to_snd

lemma Game.history_on_turn_snd_to_fst
  {α β : Type u} (g : Game α β) (turn : ℕ):
  let H := g.history_on_turn ;
  Turn_snd turn → H (turn + 1) = (g.fst_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Game.history_on_turn]
  apply History_on_turn_snd_to_fst

lemma Symm_Game.history_on_turn_fst_to_snd
  {α β : Type u} (g : Symm_Game α β) (turn : ℕ):
  let H := g.history_on_turn ;
  Turn_fst turn → H (turn + 1) = (g.snd_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game.history_on_turn]
  apply History_on_turn_fst_to_snd

lemma Symm_Game.history_on_turn_snd_to_fst
  {α β : Type u} (g : Symm_Game α β) (turn : ℕ):
  let H := g.history_on_turn ;
  Turn_snd turn → H (turn + 1) = (g.fst_strat g.init_game_state (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game.history_on_turn]
  apply History_on_turn_snd_to_fst


/-- If a property is true on the first turn, and is maintained
throughout the first players turns, then it is true for all the
first players turns
-/
lemma Invariant_fst {p : ℕ → Prop}
  (bh : p 1) (ih : ∀ turn : ℕ, Turn_fst turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, Turn_fst turn → p turn :=
  by
  intro t
  apply @Nat.induct_2_step _ t
  · intro no
    rw [Turn_fst] at no
    contradiction
  · intro
    exact bh
  · intro n a _ c
    rw [← Turn_fst_step] at c
    exact ih n c (a c)

/-- If a property is true on the zeroth turn, and is maintained
throughout the second players turns, then it is true for all the
second players turns
-/
lemma Invariant_snd {p : ℕ → Prop}
  (bh : p 0) (ih : ∀ turn : ℕ, Turn_snd turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, Turn_snd turn → p turn :=
  by
  intro t
  apply @Nat.induct_2_step _ t
  swap
  · intro no
    rw [Turn_snd] at no
    contradiction
  · intro
    exact bh
  · intro n a _ c
    rw [← Turn_snd_step] at c
    exact ih n c (a c)


/-- If a property is true on the second turn, and is maintained
throughout the second players turns, then it is true for all the
second players turns (except for maybe the zeroth).
-/
lemma Invariant_snd' {p : ℕ → Prop}
  (bh : p 2) (ih : ∀ turn : ℕ, Turn_snd turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, turn ≥ 2 → Turn_snd turn → p turn :=
  by
  intro t
  apply @Nat.induct_2_step _ t
  swap
  · intro no nope
    rw [Turn_snd] at nope
    contradiction
  · intro no
    linarith
  · intro n a _ b c
    rw [← Turn_snd_step] at c
    cases' n with m
    · apply bh
    · cases' m with k
      · rw [Turn_snd] at c
        contradiction
      · apply ih
        · apply c
        · apply a _ c
          rw [Nat.succ_eq_add_one]
          linarith

/--
Given a game world and strategies, return the state given a turn
-/
def Game_World.state_on_turn {α β : Type u} (g : Game_World α β)
    (fst_strat snd_strat: Strategy α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn fst_strat snd_strat n
         if Turn_fst (n+1)
         then g.fst_transition h (fst_strat g.init_game_state h)
         else g.snd_transition h (snd_strat g.init_game_state h)


/--
Given a game, return the state given a turn
-/
def Game.state_on_turn {α β : Type u} (g : Game α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn n
         if Turn_fst (n+1)
         then g.fst_transition h (g.fst_strat g.init_game_state h)
         else g.snd_transition h (g.snd_strat g.init_game_state h)


lemma Game.state_on_turn_toWorld {α β : Type u} (g : Game α β):
  g.toGame_World.state_on_turn g.fst_strat g.snd_strat = g.state_on_turn :=
  by
  funext n
  dsimp [Game.state_on_turn, Game_World.state_on_turn]


/--
Given a symmetric game world and strategies, return the state given a turn
-/
def Symm_Game_World.state_on_turn {α β : Type u} (g : Symm_Game_World α β)
    (fst_strat snd_strat: Strategy α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn fst_strat snd_strat n
         if Turn_fst (n+1)
         then g.transition h (fst_strat g.init_game_state h)
         else g.transition h (snd_strat g.init_game_state h)


/--
Given a symmetric game world and strategies, return the state given a turn
-/
def Symm_Game.state_on_turn {α β : Type u} (g : Symm_Game α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn n
         if Turn_fst (n+1)
         then g.transition h (g.fst_strat g.init_game_state h)
         else g.transition h (g.snd_strat g.init_game_state h)


/--
Given a game world and strategies, return the state given a turn
-/
def Game_World_wDraw.state_on_turn {α β : Type u} (g : Game_World_wDraw α β)
    (fst_strat snd_strat: Strategy α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn fst_strat snd_strat n
         if Turn_fst (n+1)
         then g.fst_transition h (fst_strat g.init_game_state h)
         else g.snd_transition h (snd_strat g.init_game_state h)


/--
Given a game, return the state given a turn
-/
def Game_wDraw.state_on_turn {α β : Type u} (g : Game_wDraw α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn n
         if Turn_fst (n+1)
         then g.fst_transition h (g.fst_strat g.init_game_state h)
         else g.snd_transition h (g.snd_strat g.init_game_state h)


lemma Symm_Game.state_on_turn_toWorld {α β : Type u} (g : Symm_Game α β):
  g.toSymm_Game_World.state_on_turn g.fst_strat g.snd_strat = g.state_on_turn :=
  by
  funext n
  dsimp [Symm_Game.state_on_turn, Symm_Game_World.state_on_turn]

@[simp]
lemma Symm_Game_World.state_on_turn_toGame_World {α β : Type u} (g : Symm_Game_World α β):
  g.toGame_World.state_on_turn = g.state_on_turn :=
  by
  funext f s n
  cases n with
  | zero => dsimp [Game_World.state_on_turn, Symm_Game_World.state_on_turn]
  | succ m =>
      dsimp [Game_World.state_on_turn, Symm_Game_World.state_on_turn]
      congr

@[simp]
lemma Symm_Game.state_on_turn_toGame {α β : Type u} (g : Symm_Game α β):
  g.toGame.state_on_turn = g.state_on_turn :=
  by
  funext n
  dsimp [Game.state_on_turn, Symm_Game.state_on_turn]



lemma Game.state_on_turn_fst_to_snd
  {α β : Type u} (g : Game α β) (turn : ℕ):
  let S := g.state_on_turn ;
  let H := g.history_on_turn turn ;
  Turn_fst (turn + 1) → S (turn + 1) = g.fst_transition H  (g.fst_strat g.init_game_state H) :=
  by
  intro S H t
  dsimp [Game.state_on_turn]
  rw [if_pos t]


lemma Game.state_on_turn_snd_to_fst
  {α β : Type u} (g : Game α β) (turn : ℕ):
  let S := g.state_on_turn ;
  let H := g.history_on_turn turn ;
  Turn_snd (turn + 1) → S (turn + 1) = g.snd_transition H  (g.snd_strat g.init_game_state H) :=
  by
  intro S H t
  dsimp [Game.state_on_turn]
  rw [← Turn_not_fst_iff_snd] at t
  rw [if_neg t]




lemma Symm_Game.state_on_turn_fst_to_snd
  {α β : Type u} (g : Symm_Game α β) (turn : ℕ):
  let S := g.state_on_turn ;
  let H := g.history_on_turn turn ;
  Turn_fst (turn + 1) → S (turn + 1) = g.transition H  (g.fst_strat g.init_game_state H) :=
  by
  intro S H t
  dsimp [Symm_Game.state_on_turn]
  rw [if_pos t]


lemma Symm_Game.state_on_turn_snd_to_fst
  {α β : Type u} (g : Symm_Game α β) (turn : ℕ):
  let S := g.state_on_turn ;
  let H := g.history_on_turn turn ;
  Turn_snd (turn + 1) → S (turn + 1) = g.transition H  (g.snd_strat g.init_game_state H) :=
  by
  intro S H t
  dsimp [Symm_Game.state_on_turn]
  rw [← Turn_not_fst_iff_snd] at t
  rw [if_neg t]





inductive Game_World_wDraw.Turn_isWLD (g : Game_World_wDraw α β) (f_strat s_strat : Strategy α β) (turn : ℕ) : Prop where
| wf : Turn_fst turn → g.fst_win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| ws : Turn_snd turn → g.snd_win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn
| d : g.draw_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWLD f_strat s_strat turn


def Game_World_wDraw.isWLD (g : Game_World_wDraw α β) : Prop :=
    ∀ f_strat s_strat : Strategy α β,
    (f_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) f_strat s_strat) →
    (s_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) f_strat s_strat) →
    ∃ turn, g.Turn_isWLD f_strat s_strat turn


structure Game_World_Terminating (α β : Type u) extends Game_World_wDraw α β where
  termination : toGame_World_wDraw.isWLD


def Game_World_wDraw.isWLD_wBound (g : Game_World_wDraw α β) (T : ℕ) : Prop :=
    ∀ f_strat s_strat : Strategy α β,
    (f_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) f_strat s_strat) →
    (s_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) f_strat s_strat) →
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

/-- The states from turn `0` to `turn - 1` -/
def Game_World.state_upto_turn {α β : Type u} (g : Game_World α β)
    (fst_strat snd_strat: Strategy α β) (turn : ℕ) : List α :=
  List.map (g.state_on_turn fst_strat snd_strat) (List.range turn)

/-- The states from turn `0` to `turn - 1` -/
def Game.state_upto_turn {α β : Type u} (g : Game α β) (turn : ℕ) : List α :=
  List.map g.state_on_turn (List.range turn)

/-- The states from turn `0` to `turn - 1` -/
def Symm_Game_World.state_upto_turn {α β : Type u} (g : Symm_Game_World α β)
    (fst_strat snd_strat: Strategy α β) (turn : ℕ) : List α :=
  List.map (g.state_on_turn fst_strat snd_strat) (List.range turn)

/-- The states from turn `0` to `turn - 1` -/
def Symm_Game.state_upto_turn {α β : Type u} (g : Symm_Game α β) (turn : ℕ) : List α :=
  List.map g.state_on_turn (List.range turn)



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
   (ws_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) ws snd_s) →
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
   (ws_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) fst_s ws) →
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
   (ws_leg : Strategy_legal_fst g.init_game_state (fun _ => g.law) ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state (fun _ => g.law) ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Symm_Game α β).fst_win


def Symm_Game_World.is_snd_win  {α β : Type u} (g : Symm_Game_World α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   (ws_leg : Strategy_legal_snd g.init_game_state (fun _ => g.law) fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state (fun _ => g.law) fst_s ws ) →
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
   (ws_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) ws snd_s) →
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
   (ws_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) fst_s ws) →
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Game α β).snd_win


def Game_World_wDraw.is_fst_draw  {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ snd_s : Strategy α β,
   (ws_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) ws snd_s) →
   (snd_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) ws snd_s) →
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Game_wDraw α β).fst_draw


def Game_World_wDraw.is_snd_draw  {α β : Type u} (g : Game_World_wDraw α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   (ws_leg : Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) fst_s ws) →
   (fst_leg : Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) fst_s ws) →
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





-- # More

lemma Symm_Game_World.mem_History_on_turn {α β : Type u} (g : Symm_Game_World α β)
    (turn : ℕ)
    (ini : α) (f_strat s_strat: Strategy α β)
    (x : β) :
    let H := History_on_turn ini f_strat s_strat ;
    x ∈ H (turn) ↔ (∃ t < turn, ((Turn_fst (t+1) ∧ x = f_strat ini (H t)) ∨ (Turn_snd (t+1) ∧ x = s_strat ini (H t)))) :=
    -- for ↑, recall that `f_strat ini (H t)` is the action of turn `t+1`
    by
    intro H
    apply @Nat.strong_induction_on (fun turn => x ∈ H (turn) ↔ (∃ t < turn, (Turn_fst (t+1) ∧ x = f_strat ini (H t)) ∨ (Turn_snd (t+1) ∧ x = s_strat ini (H t)))) turn
    intro n ih
    cases' n with z s
    · dsimp [H, History_on_turn]
      simp only [List.not_mem_nil, not_lt_zero', false_and, exists_const]
    · dsimp [H, History_on_turn]
      split_ifs
      · constructor
        · intro c
          rw [List.mem_cons] at c
          cases' c with f hi
          · use z
            use (by exact Nat.le.refl)
            left
            rename_i l
            exact ⟨l,f⟩
          · specialize ih z (by exact Nat.le.refl)
            obtain ⟨t, tl, tp⟩ := ih.mp hi
            use t
            use (by apply lt_trans tl ; exact Nat.lt.base z)
        · rintro ⟨t,⟨tl,tp⟩⟩
          rw [List.mem_cons]
          cases' tp with f s
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              left
              exact f
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              rw [this] at f
              left
              exact f.2
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              right
              exact s
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              rw [this] at s
              rename_i no
              rw [← Turn_not_snd_iff_fst] at no
              exfalso
              exact no s.1
      · constructor
        · intro c
          rw [List.mem_cons] at c
          cases' c with f hi
          · use z
            use (by exact Nat.le.refl)
            right
            rename_i l
            exact ⟨l,f⟩
          · specialize ih z (by exact Nat.le.refl)
            obtain ⟨t, tl, tp⟩ := ih.mp hi
            use t
            use (by apply lt_trans tl ; exact Nat.lt.base z)
        · rintro ⟨t,⟨tl,tp⟩⟩
          rw [List.mem_cons]
          cases' tp with f s
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              left
              exact f
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              rw [this] at f
              rename_i no
              exfalso
              exact no f.1
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              right
              exact s
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              rw [this] at s
              left
              exact s.2


lemma History_on_turn_nonempty_of_succ
  (ini : α) (f_strat s_strat: Strategy α β) {t : ℕ} :
  History_on_turn ini f_strat s_strat (t+1) ≠ [] :=
  by
  dsimp [History_on_turn]
  split_ifs <;> decide


lemma History_on_turn_zero
  (ini : α) (f_strat s_strat: Strategy α β) :
  History_on_turn ini f_strat s_strat 0 = [] :=
  by rfl
