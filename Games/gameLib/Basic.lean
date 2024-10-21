/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.TurnAPI

#check 1

/-
This file defines the basic notions of games & stategies.
It can be read top down.

Important notions:
- `Game_World`, `Symm_Game_World` and `Game_World_wDraw`
- `Game`, `Symm_Game` and `Game_World`
- `hist_neutral`, `hist_legal`, `hist_on_turn`
- `fStrategy` and `sStrategy`

-/



-- # Game worlds

/--
A `Game_World` requires two types: one for the state of the game,
one for the type of moves.

It is given by the following data:
- an initial state of the game
- two predicates to tell, given a list of the moves played so far
  (and implicitly the initial state), whether the game is a victory
  for the corresponding player.
- two predicates to tell, given a list of the moves played so far
  (and implicitly the initial state), whether an action is considered
  legal, and may be play at that stage in the game.
- two transition function that, given a list of the moves played so far
  and the latest move (and implicitly the initial state), return the
  state after this move.
-/
structure Game_World (α β : Type _) where
  init_game_state : α
  fst_win_states : List β →  Prop
  snd_win_states : List β → Prop
  fst_legal : List β → (β → Prop)
  snd_legal : List β → (β → Prop)
  fst_transition : List β → β → α
  snd_transition : List β → β → α

/--
A `Game_World_wDraw` extends a `Game_World` with the possibility of a draw,
which is determined by a predicate on the history so far.
-/
structure Game_World_wDraw (α β : Type _) extends Game_World α β where
  draw_states : List β → Prop



@[simp]
lemma Game_World_wDraw.toGame_World_ini {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.init_game_state = g.init_game_state :=
  by
  rfl

@[simp]
lemma Game_World_wDraw.toGame_World_fst_win {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.fst_win_states = g.fst_win_states :=
  by
  rfl

@[simp]
lemma Game_World_wDraw.toGame_World_snd_win {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.snd_win_states = g.snd_win_states :=
  by
  rfl

@[simp]
lemma Game_World_wDraw.toGame_World_fst_trans {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.fst_transition = g.fst_transition :=
  by
  rfl

@[simp]
lemma Game_World_wDraw.toGame_World_snd_trans {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.snd_transition = g.snd_transition :=
  by
  rfl

@[simp]
lemma Game_World_wDraw.toGame_World_fst_legal {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.fst_legal = g.fst_legal :=
  by
  rfl

@[simp]
lemma Game_World_wDraw.toGame_World_snd_legal {α β : Type _} (g : Game_World_wDraw α β) :
  g.toGame_World.snd_legal = g.snd_legal :=
  by
  rfl


/--
A `Symm_Game_World` is simlar to a `Game_World`, with the distinction
that the transition functions and the predicates to tell legality of
moves are the same for both players.

The win-predicates are distinct, as they should take into account wether
the current turn is the first or the second player's.
-/
structure Symm_Game_World (α β : Type _) where
  init_game_state : α
  fst_win_states : List β →  Prop
  snd_win_states : List β → Prop
  transition : List β → β → α
  law : List β → (β → Prop)


def Symm_Game_World.toGame_World {α β : Type _} (g : Symm_Game_World α β) : Game_World α β :=
  {init_game_state := g.init_game_state
   fst_win_states := g.fst_win_states
   fst_transition := g.transition
   fst_legal := g.law
   snd_win_states := g.snd_win_states
   snd_transition := g.transition
   snd_legal := g.law
   }


instance {α β : Type _} : Coe (Symm_Game_World α β) (Game_World α β) where
  coe := Symm_Game_World.toGame_World

@[simp]
lemma Symm_Game_World.toGame_World_ini {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.init_game_state = g.init_game_state :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_fst_win {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.fst_win_states = g.fst_win_states :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_win {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.snd_win_states = g.snd_win_states :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_fst_trans {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.fst_transition = g.transition :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_trans {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.snd_transition = g.transition :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_fst_legal {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.fst_legal = g.law :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_legal {α β : Type _} (g : Symm_Game_World α β) :
  g.toGame_World.snd_legal = g.law :=
  by
  rfl


-- # Neutrality

structure Game_World.hist_neutral (g : Game_World α β) (hist : List β) : Prop where
  not_fst : ¬ g.fst_win_states hist
  not_snd : ¬ g.snd_win_states hist

structure Game_World_wDraw.hist_neutral (g : Game_World_wDraw α β) (hist : List β) extends Game_World.hist_neutral g.toGame_World hist : Prop where
  not_draw : ¬ g.draw_states hist

def Symm_Game_World.hist_neutral (g : Symm_Game_World α β) (hist : List β) : Prop :=
  g.toGame_World.hist_neutral hist

instance (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] :
  DecidablePred (g.hist_neutral) :=
  by
  intro hist
  rename_i I I'
  specialize I hist
  specialize I' hist
  match I, I' with
  | .isFalse t1, .isFalse t2 => exact .isTrue ⟨t1,t2⟩
  | .isTrue t , _ => apply isFalse ; intro con ; exact con.not_fst t
  | _ , .isTrue t => apply isFalse ; intro con ; exact con.not_snd t


lemma Game_World.hist_neutral_and (g : Game_World α β) (hist : List β) :
  g.hist_neutral hist ↔ (¬ g.fst_win_states hist ∧ ¬ g.snd_win_states hist) := by
  constructor
  · intro h
    exact ⟨h.not_fst, h.not_snd⟩
  · intro h
    exact ⟨h.1, h.2⟩





-- # Legality


/--
A history of moves is considered legal, if it is either empty,
or the history up to the latest move was legal, and the latest move
is legal wrt. the predicate of the player who's turn it was.

Note that turn 0 is considered no ones turn, and for turns ≥ 1,
odd turns are the first players turns, and even ones the second
players turns.
-/
inductive Game_World.hist_legal (g : Game_World α β)  : List β → Prop
| nil : g.hist_legal []
| cons (l : List β) (act : β) : (if Turn_fst (l.length + 1)
                                then g.fst_legal l act
                                else g.snd_legal l act) → g.hist_legal l →  g.hist_legal (act :: l)


def Game_World_wDraw.hist_legal (g : Game_World_wDraw α β) (hist : List β) : Prop :=
  g.toGame_World.hist_legal hist

def Symm_Game_World.hist_legal (g : Symm_Game_World α β) (hist : List β) : Prop :=
  g.toGame_World.hist_legal hist


instance (g : Game_World α β)
  [∀ h : List β, DecidablePred (g.fst_legal h)] [∀ h : List β, DecidablePred (g.snd_legal h)] :
  DecidablePred (g.hist_legal) :=
  by
  intro hist
  induction' hist with x l ih
  · apply isTrue
    apply Game_World.hist_legal.nil
  · cases' ih with ih ih
    · apply isFalse
      intro con
      cases' con
      rename_i no nope
      exact ih no
    · exact (if h : Turn_fst (l.length + 1)
             then (by
                   rename_i I I'
                   specialize I l x
                   cases' I with I I
                   · apply isFalse
                     intro con
                     cases' con
                     rename_i no
                     rw [if_pos h] at no
                     exact I no
                   · apply isTrue
                     apply Game_World.hist_legal.cons _ _ _ ih
                     rw [if_pos h]
                     exact I
                  )
             else (by
                   rename_i I I'
                   specialize I' l x
                   cases' I' with I' I'
                   · apply isFalse
                     intro con
                     cases' con
                     rename_i no
                     rw [if_neg h] at no
                     exact I' no
                   · apply isTrue
                     apply Game_World.hist_legal.cons _ _ _ ih
                     rw [if_neg h]
                     exact I'))



-- # Strategies


/--
A strategy is a function that given
- the game world (hence also the initial state),
- the history of moves of both players so far, in the form of a list of moves
- a certificate that it is the players turn
- a certificate that the history is made of legal moves

returns an action to be played and a certificate that this action
is legal at this stage.
-/
def Game_World.fStrategy (g : Game_World α β) :=
  (hist : List β) → (Turn_fst (hist.length+1)) →
  (g.hist_legal hist) →
  { act : β // g.fst_legal hist act}


/--
A strategy is a function that given
- the game world (hence also the initial state),
- the history of moves of both players so far, in the form of a list of moves
- a certificate that it is the players turn
- a certificate that the history is made of legal moves

returns an action to be played and a certificate that this action
is legal at this stage.
-/
def Game_World.sStrategy (g : Game_World α β) :=
  (hist : List β) → (Turn_snd (hist.length+1)) →
  (g.hist_legal hist) →
  { act : β // g.snd_legal hist act}

def Game_World_wDraw.fStrategy (g : Game_World_wDraw α β) :=
  g.toGame_World.fStrategy

def Game_World_wDraw.sStrategy (g : Game_World_wDraw α β) :=
  g.toGame_World.sStrategy

def Symm_Game_World.fStrategy (g : Symm_Game_World α β) :=
  g.toGame_World.fStrategy

def Symm_Game_World.sStrategy (g : Symm_Game_World α β) :=
  g.toGame_World.sStrategy



-- # Histories


/--
Given a game world and two strategies for players to play in it,
`hist_on_turn` is a function that returns the list of moves played
by the players, according to their strategies, given a turn.
-/
def Game_World.hist_on_turn (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) : {hist : List β // g.hist_legal hist ∧ hist.length = t} :=
  match t with
  | 0 => ⟨[], ⟨Game_World.hist_legal.nil, rfl⟩⟩
  | n+1 =>  let h := g.hist_on_turn fst_strat snd_strat n
            if T : Turn_fst (n+1)
            then
              let T' : Turn_fst (List.length h.val + 1) := by rw [h.property.2] ; exact T ;
              let act := (fst_strat h.val T' h.property.1).val ;
              let leg := (fst_strat h.val T' h.property.1).property ;
              ⟨ act :: h.val , ⟨Game_World.hist_legal.cons h.val act (by rw [if_pos T'] ; exact leg) h.property.1, (by dsimp ; rw [h.property.2])⟩⟩
            else
              let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
              let act := (snd_strat h.val T' h.property.1).val ;
              let leg := (snd_strat h.val T' h.property.1).property ;
              ⟨ act :: h.val , ⟨Game_World.hist_legal.cons h.val act (by rw [if_neg ] ; exact leg ; rw [Turn_not_fst_iff_snd] ; exact T') h.property.1, (by dsimp ; rw [h.property.2])⟩⟩

def Symm_Game_World.hist_on_turn (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) : {hist : List β // g.hist_legal hist ∧ hist.length = t} :=
  @Game_World.hist_on_turn _ _  g.toGame_World (by rwa [g.toGame_World_fst_win]) (by rwa [g.toGame_World_snd_win]) fst_strat snd_strat t


def Game_World_wDraw.hist_on_turn (g : Game_World_wDraw α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) : {hist : List β // g.hist_legal hist ∧ hist.length = t} :=
  g.toGame_World.hist_on_turn fst_strat snd_strat t




-- # Games

structure Game (α β : Type _) extends Game_World α β where
  fst_strat : toGame_World.fStrategy
  snd_strat : toGame_World.sStrategy

structure Symm_Game (α β : Type _) extends Symm_Game_World α β where
  fst_strat : toSymm_Game_World.fStrategy
  snd_strat : toSymm_Game_World.sStrategy

def Symm_Game.toGame {α β : Type _} (g : Symm_Game α β) : Game α β :=
 {toGame_World :=  Symm_Game_World.toGame_World (g.toSymm_Game_World)
  fst_strat := g.fst_strat
  snd_strat := g.snd_strat
  }

structure Game_wDraw (α β : Type _) extends Game_World_wDraw α β where
  fst_strat : toGame_World_wDraw.fStrategy
  snd_strat : toGame_World_wDraw.sStrategy


def Game.hist_on_turn (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) : {hist : List β // g.hist_legal hist ∧ hist.length = t} :=
  g.toGame_World.hist_on_turn g.fst_strat g.snd_strat t


lemma Symm_Game.toGame_fst_win (g : Symm_Game α β) :
  g.toGame.fst_win_states = g.fst_win_states := rfl


lemma Symm_Game.toGame_snd_win (g : Symm_Game α β) :
  g.toGame.snd_win_states = g.snd_win_states := rfl



-- # State


def Game_World.state_from_hist (g : Game_World α β) : List β → α
| [] => g.init_game_state
| a :: h => if Turn_fst (h.length +1)
            then g.fst_transition h a
            else g.snd_transition h a

def Game_World.state_on_turn (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy) (snd_strat : g.sStrategy) : ℕ → α
  | 0 => g.init_game_state
  | n+1 => let h := g.hist_on_turn fst_strat snd_strat n
          if T : Turn_fst (n+1)
          then let T' : Turn_fst (List.length h.val + 1) := by rw [h.property.2] ; exact T ;
                g.fst_transition h (fst_strat h.val T' h.property.1)
          else let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
                g.snd_transition h (snd_strat h.val T' h.property.1)
