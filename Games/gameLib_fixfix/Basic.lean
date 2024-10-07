/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic
import Mathlib.Data.List.DropRight -- now Rdrop, or not


-- should contain game structures, turn manipulations, history and state lemmas


-- # Environments



/--
The game world for state type α and action type β.
-/
structure Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the first player-/
  fst_win_states : α → List β →  Prop
  /-- A predicate that decides in which states the game is won for the second player-/
  snd_win_states : α → List β → Prop
  /-- Given the initial state and the history, return a predicate
  that determines the legal actions for the first player-/
  fst_legal : α → List β → (β → Prop)
  /-- Given the initial state and the history, return a predicate
  that determines the legal actions for the second player-/
  snd_legal : α → List β → (β → Prop)
  /-- Given the initial state, the history, and an action of the frist player,
  , and return next state-/
  fst_transition : α → List β → β → α
  /-- Given the initial state, the history, and an action of the second player,
   and return next state-/
  snd_transition : α → List β → β → α


/-- `Game_World` with addtional drawing states, given by a predicate on states-/
structure Game_World_wDraw (α β : Type u) extends Game_World α β where
  draw_states : α → List β → Prop


/--
The game world for state type α and action type β, where players aren't discerened.
-/
structure Symm_Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the players-/
  fst_win_states : α → List β →  Prop
  /-- A predicate that decides in which states the game is won for the second player-/
  snd_win_states : α → List β → Prop
  /-- Given  the history, and an action of the player, return next state-/
  transition : α → List β → β → α
  /-- A predicate that decides in which states the game is won for the players-/
  law : α → List β → (β → Prop)



/--
Produce a `Game_World` from a `Symm_Game_World`.
-/
def Symm_Game_World.toGame_World {α β : Type u} (g : Symm_Game_World α β) : Game_World α β :=
  {init_game_state := g.init_game_state
   fst_win_states := g.fst_win_states
   fst_transition := g.transition
   fst_legal := g.law
   snd_win_states := g.snd_win_states
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
  g.toGame_World.fst_win_states = g.fst_win_states :=
  by
  rfl

@[simp]
lemma Symm_Game_World.toGame_World_snd_win {α β : Type u} (g : Symm_Game_World α β) :
  g.toGame_World.snd_win_states = g.snd_win_states :=
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



-- # Turns



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



lemma Turn_not_fst_iff_snd (turn : ℕ) : (¬ Turn_fst turn) ↔ Turn_snd turn :=
  by rw [Turn_fst, Turn_snd]

lemma Turn_not_snd_iff_fst (turn : ℕ) : (¬ Turn_snd turn) ↔ Turn_fst turn :=
  by rw [Turn_fst, Turn_snd, not_ne_iff]

lemma Turn_snd_iff_not_fst (turn : ℕ) : Turn_snd turn ↔ (¬ Turn_fst turn) :=
  by rw [Turn_fst, Turn_snd]

lemma Turn_fst_iff_not_snd (turn : ℕ) : Turn_fst turn ↔ (¬ Turn_snd turn) :=
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


lemma Turn_fst_not_step' (turn : ℕ): ¬ Turn_fst turn ↔ Turn_fst (turn + 1) :=
  by
  rw [not_iff_comm, Iff.comm , Turn_fst_not_step]



lemma Turn_snd_not_step' (turn : ℕ): ¬ Turn_snd turn ↔  Turn_snd (turn + 1) :=
  by
  rw [not_iff_comm, Iff.comm , Turn_snd_not_step]


lemma Turn_add_fst_fst (a b : ℕ) : Turn_fst a → Turn_fst b → Turn_snd (a+b) :=
  by
  intro A B
  dsimp [Turn_fst, Turn_snd] at *
  rw [Nat.mod_two_ne_one, Nat.add_mod, A, B]
  decide


lemma Turn_add_fst_snd (a b : ℕ) : Turn_fst a → Turn_snd b → Turn_fst (a+b) :=
  by
  intro A B
  dsimp [Turn_fst, Turn_snd] at *
  rw [Nat.mod_two_ne_one] at B
  rw [Nat.add_mod, A, B]
  decide

lemma Turn_add_snd_fst (a b : ℕ) : Turn_snd a → Turn_fst b → Turn_fst (a+b) :=
  by
  intro A B
  dsimp [Turn_fst, Turn_snd] at *
  rw [Nat.mod_two_ne_one] at A
  rw [Nat.add_mod, A, B]
  decide

lemma Turn_add_snd_snd (a b : ℕ) : Turn_snd a → Turn_snd b → Turn_snd (a+b) :=
  by
  intro A B
  dsimp [Turn_fst, Turn_snd] at *
  rw [Nat.mod_two_ne_one] at *
  rw [Nat.add_mod, A, B]
  decide


/-- If a property is true on the first turn, and is maintained
throughout the first players turns, then it is true for all the
first players turns
-/
lemma Invariant_fst {p : ℕ → Prop}
  (bh : p 1) (ih : ∀ turn : ℕ, Turn_fst turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, Turn_fst turn → p turn :=
  by
  intro t
  apply Nat.twoStepInduction _ _ _ t
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
  apply Nat.twoStepInduction _ _ _ t
  swap
  · intro no
    rw [Turn_snd] at no
    contradiction
  · intro
    exact bh
  · intro n a _ c
    rw [← Turn_snd_step] at c
    exact ih n c (a c)

lemma Invariant_snd' {p : ℕ → Prop}
  (bh : p 2) (ih : ∀ turn : ℕ, Turn_snd turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, turn ≥ 2 → Turn_snd turn → p turn :=
  by
  intro t
  apply Nat.twoStepInduction _ _ _ t
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



-- # History and strategies

inductive Hist_legal (ini : α) (f_law s_law : α → List β → (β → Prop))  : List β → Prop
| nil : Hist_legal ini f_law s_law  []
| cons (l : List β) (act : β) : (if Turn_fst (l.length + 1)
                                then f_law ini l act
                                else s_law ini l act) → Hist_legal ini f_law s_law  l →  Hist_legal ini f_law s_law (act :: l)


instance (f_law s_law : α → List β → (β → Prop)) [∀ i : α, ∀ h : List β, DecidablePred (f_law i h)] [∀ i : α, ∀ h : List β, DecidablePred (s_law i h)] (ini : α) : DecidablePred (Hist_legal ini f_law s_law) :=
  by
  intro hist
  induction' hist with x l ih
  · apply isTrue
    apply Hist_legal.nil
  · cases' ih with ih ih
    · apply isFalse
      intro con
      cases' con
      rename_i no nope
      exact ih no
    · exact (if h : Turn_fst (l.length + 1)
             then (by
                   rename_i I I'
                   specialize I ini l x
                   cases' I with I I
                   · apply isFalse
                     intro con
                     cases' con
                     rename_i no
                     rw [if_pos h] at no
                     exact I no
                   · apply isTrue
                     apply Hist_legal.cons _ _ _ ih
                     rw [if_pos h]
                     exact I
                  )
             else (by
                   rename_i I I'
                   specialize I' ini l x
                   cases' I' with I' I'
                   · apply isFalse
                     intro con
                     cases' con
                     rename_i no
                     rw [if_neg h] at no
                     exact I' no
                   · apply isTrue
                     apply Hist_legal.cons _ _ _ ih
                     rw [if_neg h]
                     exact I'))




def fStrategy (ini : α) (f_law s_law : α → List β → (β → Prop)) :=
  (hist : List β) → (Turn_fst (hist.length+1)) → (Hist_legal ini f_law s_law hist) → { act : β // f_law ini hist act}

def sStrategy (ini : α) (f_law s_law : α → List β → (β → Prop)) :=
  (hist : List β) → (Turn_snd (hist.length+1)) → (Hist_legal ini f_law s_law hist) → { act : β // s_law ini hist act}



def History_on_turn
    (ini : α) (f_law s_law : α → List β → (β → Prop))
    (fst_strat : fStrategy ini f_law s_law)  (snd_strat : sStrategy ini f_law s_law) : (t : ℕ) → {hist : List β // Hist_legal ini f_law s_law hist ∧ hist.length = t}
| 0 => ⟨[], ⟨Hist_legal.nil, rfl⟩⟩
| n+1 => let h := History_on_turn ini f_law s_law fst_strat snd_strat n
         if T : Turn_fst (n+1)
         then
            let T' : Turn_fst (List.length h.val + 1) := by rw [h.property.2] ; exact T ;
            let act := (fst_strat h.val T' h.property.1).val ;
            let leg := (fst_strat h.val T' h.property.1).property ;
            ⟨ act :: h.val , ⟨Hist_legal.cons h.val act (by rw [if_pos T'] ; exact leg) h.property.1, (by dsimp ; rw [h.property.2])⟩⟩
         else
            let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
            let act := (snd_strat h.val T' h.property.1).val ;
            let leg := (snd_strat h.val T' h.property.1).property ;
            ⟨ act :: h.val , ⟨Hist_legal.cons h.val act (by rw [if_neg ] ; exact leg ; rw [Turn_not_fst_iff_snd] ; exact T') h.property.1, (by dsimp ; rw [h.property.2])⟩⟩


lemma History_on_turn_length (ini : α) (f_law s_law : α → List β → (β → Prop))
  (fst_strat : fStrategy ini f_law s_law)  (snd_strat : sStrategy ini f_law s_law) (t : Nat) :
  (History_on_turn ini f_law s_law fst_strat snd_strat t).val.length = t :=
  by
  apply (History_on_turn ini f_law s_law fst_strat snd_strat t).property.2




-- # Games

structure Game (α β : Type u) extends Game_World α β where
  /-- The first players strategy-/
  fst_strat : fStrategy (toGame_World.init_game_state) toGame_World.fst_legal toGame_World.snd_legal
  /-- The second players strategy-/
  snd_strat : sStrategy (toGame_World.init_game_state) toGame_World.fst_legal toGame_World.snd_legal


/-- Same as `Game`, but for a symmetric game world-/
structure Symm_Game (α β : Type u) extends Symm_Game_World α β where
  /-- The first players strategy-/
  fst_strat : fStrategy (toSymm_Game_World.init_game_state) toSymm_Game_World.law toSymm_Game_World.law
  /-- The second players strategy-/
  snd_strat : sStrategy (toSymm_Game_World.init_game_state) toSymm_Game_World.law toSymm_Game_World.law



/-- Build a `Game` from a `Symm_Game`-/
def Symm_Game.toGame {α β : Type u} (g : Symm_Game α β) : Game α β :=
 {toGame_World :=  Symm_Game_World.toGame_World (g.toSymm_Game_World)
  fst_strat := g.fst_strat
  snd_strat := g.snd_strat
  }

/-- ADD DOCS-/
structure Game_wDraw (α β : Type u) extends Game_World_wDraw α β where
  /-- The first players strategy-/
  fst_strat : fStrategy (toGame_World.init_game_state) toGame_World.fst_legal toGame_World.snd_legal
  /-- The second players strategy-/
  snd_strat : sStrategy (toGame_World.init_game_state) toGame_World.fst_legal toGame_World.snd_legal


@[simp]
lemma Symm_Game.toGame_ini {α β : Type u} (g : Symm_Game α β) :
  g.toGame.init_game_state = g.init_game_state :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_fst_win {α β : Type u} (g : Symm_Game α β) :
  g.toGame.fst_win_states = g.fst_win_states :=
  by
  rfl

@[simp]
lemma Symm_Game.toGame_snd_win {α β : Type u} (g : Symm_Game α β) :
  g.toGame.snd_win_states = g.snd_win_states :=
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


-- # History of games


/-- History for a given turn, given a game world and stategies-/
def Game_World.history_on_turn {α β : Type u} (g : Game_World α β)
    (fst_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (snd_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) :
    (t : ℕ) → { hist // Hist_legal g.init_game_state g.fst_legal g.snd_legal hist ∧ List.length hist = t } :=
    History_on_turn g.init_game_state g.fst_legal g.snd_legal fst_strat snd_strat

def Symm_Game_World.history_on_turn {α β : Type u} (g : Symm_Game_World α β)
    (fst_strat : fStrategy g.init_game_state g.law g.law) (snd_strat : sStrategy g.init_game_state g.law g.law) :
    (t : ℕ) → { hist // Hist_legal g.init_game_state g.law g.law hist ∧ List.length hist = t } :=
    Game_World.history_on_turn g.toGame_World fst_strat snd_strat


def Game.history_on_turn {α β : Type _} (g : Game α β) :
  (t : ℕ) → { hist // Hist_legal g.init_game_state g.fst_legal g.snd_legal hist ∧ List.length hist = t } :=
  Game_World.history_on_turn g.toGame_World g.fst_strat g.snd_strat

def Symm_Game.history_on_turn {α β : Type _} (g : Symm_Game α β) :
  (t : ℕ) → { hist // Hist_legal g.init_game_state g.law g.law hist ∧ List.length hist = t } :=
  Symm_Game_World.history_on_turn g.toSymm_Game_World g.fst_strat g.snd_strat


lemma Game_World.history_on_turn_def {α β : Type u} (g : Game_World α β) :
    g.history_on_turn = History_on_turn g.init_game_state g.fst_legal g.snd_legal :=
    by
    rfl

-- TODO : port initial stuff


-- # State of games

def Game_World.state_on_turn {α β : Type _} (g : Game_World α β)
    (fst_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (snd_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn fst_strat snd_strat n
         if T : Turn_fst (n+1)
         then let T' : Turn_fst (List.length h.val + 1) := by rw [h.property.2] ; exact T ;
              g.fst_transition g.init_game_state h (fst_strat h.val T' h.property.1)
         else let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
              g.snd_transition g.init_game_state h (snd_strat h.val T' h.property.1)

def Game.state_on_turn {α β : Type _} (g : Game α β) : ℕ → α :=
  Game_World.state_on_turn g.toGame_World g.fst_strat g.snd_strat

def Symm_Game_World.state_on_turn {α β : Type _} (g : Symm_Game_World α β)
  (fst_strat : fStrategy g.init_game_state g.law g.law) (snd_strat : sStrategy g.init_game_state g.law g.law) : ℕ → α :=
  Game_World.state_on_turn g.toGame_World fst_strat snd_strat

def Symm_Game.state_on_turn {α β : Type _} (g : Symm_Game α β) : ℕ → α :=
  Symm_Game_World.state_on_turn g.toSymm_Game_World g.fst_strat g.snd_strat

def State_from_history (ini : α ) (f_trans s_trans : α → List β → (β → α)) : List β → α
| [] => ini
| a :: h => if Turn_fst (h.length +1)
            then f_trans ini h a
            else s_trans ini h a

lemma Game_World.state_on_turn_State_from_history (g : Game_World α β)
    (fst_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
    (snd_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal)
    (t : ℕ) :
    g.state_on_turn fst_strat snd_strat t =
    State_from_history g.init_game_state g.fst_transition g.snd_transition
    (History_on_turn g.init_game_state g.fst_legal g.snd_legal fst_strat snd_strat t).val :=
    by
    cases' t with t
    · dsimp!
    · dsimp [state_on_turn, History_on_turn]
      split_ifs with T
      · dsimp [State_from_history]
        simp_rw [History_on_turn_length]
        rw [if_pos T]
        rfl
      · dsimp [State_from_history]
        simp_rw [History_on_turn_length]
        rw [if_neg T]
        rfl


-- TODO : port initial stuff


-- # Properties of History


lemma History_on_turn_fst_to_snd (ini : α) (f_law s_law : α → List β → (β → Prop))
    (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law) (turn : ℕ):
  let H := History_on_turn ini f_law s_law f_strat s_strat ;
  (T : Turn_fst turn) → (H (turn + 1)).val = (s_strat (H turn).val (by rw [(H turn).property.2, ← Turn_fst_snd_step] ; exact T)  (H turn).property.1).val :: (H turn).val :=
  by
  intro H tf
  dsimp [H, History_on_turn]
  rw [dif_neg ((Turn_fst_not_step turn).mp tf)]

lemma History_on_turn_snd_to_fst (ini : α) (f_law s_law : α → List β → (β → Prop))
    (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law) (turn : ℕ):
  let H := History_on_turn ini f_law s_law f_strat s_strat ;
  (T : Turn_snd turn) → (H (turn + 1)).val = (f_strat (H turn).val (by rw [(H turn).property.2, ← Turn_snd_fst_step] ; exact T)  (H turn).property.1).val :: (H turn).val :=
  by
  intro H tf
  dsimp [H, History_on_turn]
  rw [dif_pos ((Turn_snd_fst_step turn).mp tf)]


lemma Hist_legal_suffix (ini : α) (f_law s_law : α → List β → (β → Prop)) (pre post : List β) :
  Hist_legal ini f_law s_law (post ++ pre) → Hist_legal ini f_law s_law pre :=
  by
  intro main
  induction' post with x l ih
  · rw [List.nil_append] at main
    exact main
  · cases' main
    rename_i yes _
    exact ih yes


-- to mathlib
theorem List.rdrop_append_rtake : ∀ (n : Nat) (l : List α), List.rdrop l n ++ List.rtake l n = l :=
  by
  unfold List.rdrop List.rtake
  intro n l
  apply List.take_append_drop


lemma Hist_legal_rtake (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) (t : Nat) :
  Hist_legal ini f_law s_law hist → Hist_legal ini f_law s_law (hist.rtake t) := by
  intro main
  rw [← hist.rdrop_append_rtake t] at main
  apply Hist_legal_suffix _ _ _ _ _ main



lemma mem_History_on_turn {α β : Type _}
    (ini : α) (f_law s_law : α → List β → (β → Prop))
    (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law)
    (turn : ℕ) (x : β) :
    let H := History_on_turn ini f_law s_law f_strat s_strat ;
    x ∈ (H (turn)).val ↔ (∃ t < turn, if T : (Turn_fst (t+1)) then x = ((f_strat (H t).val (by rw [History_on_turn_length] ; exact T) (H t).property.1).val) else  (x = (s_strat (H t).val (by rw [History_on_turn_length] ; rw [Turn_not_fst_iff_snd] at T ; exact T) (H t).property.1).val)) :=
    -- for ↑, recall that `f_strat ini (H t)` is the action of turn `t+1`
    by
    intro H
    apply @Nat.strong_induction_on (fun turn => x ∈ (H (turn)).val ↔ (∃ t < turn, if T : (Turn_fst (t+1)) then x = ((f_strat (H t).val (by rw [History_on_turn_length] ; exact T) (H t).property.1).val) else  (x = (s_strat (H t).val (by rw [History_on_turn_length] ; rw [Turn_not_fst_iff_snd] at T ; exact T) (H t).property.1).val))) turn
    intro n ih
    cases' n with z s
    · dsimp [H, History_on_turn]
      simp only [List.not_mem_nil, not_lt_zero', false_and, exists_const]
    · dsimp [H, History_on_turn]
      split_ifs with T
      · constructor
        · intro c
          rw [List.mem_cons] at c
          cases' c with f hi
          · use z
            use (by exact Nat.le.refl)
            rw [dif_pos T]
            exact f
          · specialize ih z (by exact Nat.le.refl)
            obtain ⟨t, tl, tp⟩ := ih.mp hi
            use t
            use (by apply lt_trans tl ; exact Nat.lt.base z)
        · rintro ⟨t,⟨tl,tp⟩⟩
          rw [List.mem_cons]
          split_ifs at tp with f
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              rw [dif_pos f]
              exact tp
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              --rw [this] at tp
              left
              convert tp
              · apply this.symm
              · apply this.symm
              · apply this.symm
              · apply this.symm
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              rw [dif_neg f]
              exact tp
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              rw [this] at f
              exfalso
              exact f T
      · constructor
        · intro c
          rw [List.mem_cons] at c
          cases' c with f hi
          · use z
            use (by exact Nat.le.refl)
            rw [dif_neg T]
            exact f
          · specialize ih z (by exact Nat.le.refl)
            obtain ⟨t, tl, tp⟩ := ih.mp hi
            use t
            use (by apply lt_trans tl ; exact Nat.lt.base z)
        · rintro ⟨t,⟨tl,tp⟩⟩
          rw [List.mem_cons]
          split_ifs at tp with f
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              rw [dif_pos f]
              exact tp
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              rw [this] at f
              exfalso
              exact T f
          · specialize ih z (by exact Nat.le.refl)
            by_cases q : t < z
            · right
              rw [ih]
              use t
              use q
              rw [dif_neg f]
              exact tp
            · have : t = z := by exact Nat.eq_of_lt_succ_of_not_lt tl q
              --rw [this] at tp
              left
              convert tp
              · apply this.symm
              · apply this.symm
              · apply this.symm
              · apply this.symm




lemma History_on_turn_nonempty_of_succ
  (ini : α) (f_law s_law : α → List β → (β → Prop))
  (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law) {t : ℕ} :
  (History_on_turn ini f_law s_law f_strat s_strat (t+1)).val ≠ [] :=
  by
  dsimp [History_on_turn]
  split_ifs <;> decide


lemma History_on_turn_zero
  (ini : α) (f_law s_law : α → List β → (β → Prop))
  (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law) :
  (History_on_turn ini f_law s_law f_strat s_strat 0).val = [] :=
  by rfl

lemma History_on_turn_getLast_fst_act (ini : α) (f_law s_law : α → List β → (β → Prop))
  (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law) :
  ∀ t : ℕ, (History_on_turn ini f_law s_law f_strat s_strat (t+1)).val.getLast (by apply History_on_turn_nonempty_of_succ)
    = f_strat [] (by dsimp ; decide) (by apply Hist_legal.nil):=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    simp_rw [dif_pos (show Turn_fst (0 + 1) from (by decide))]
    dsimp [List.getLast]
  · dsimp [History_on_turn] at *
    by_cases  q : Turn_fst (Nat.succ t + 1)
    · simp_rw [dif_pos q]
      rw [List.getLast_cons]
      · exact ih
    · simp_rw [dif_neg q]
      rw [List.getLast_cons]
      · exact ih



lemma History_eq_of_strat_strong_eq (ini : α) (f_law s_law : α → List β → (β → Prop))
  (f_strat F_strat : fStrategy ini f_law s_law)  (s_strat S_strat : sStrategy ini f_law s_law)
  (T : Nat)
  (hf : ∀ hist : List β, (leg : Hist_legal ini f_law s_law hist) → (τ : Turn_fst (List.length hist + 1)) →  hist.length ≤ T → (f_strat hist τ leg).val = (F_strat hist τ leg).val)
  (hs : ∀ hist : List β, (leg : Hist_legal ini f_law s_law hist) → (τ : Turn_snd (List.length hist + 1)) →  hist.length ≤ T → (s_strat hist τ leg).val = (S_strat hist τ leg).val) :
  ∀ t ≤ (T+1), History_on_turn ini f_law s_law f_strat s_strat t = History_on_turn ini f_law s_law F_strat S_strat t :=
  by
  intro t tle
  induction' t with t ih
  · dsimp [History_on_turn]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [dif_pos q, dif_pos q]
      specialize ih (by apply le_trans _ tle ; exact Nat.le.step Nat.le.refl)
      --dsimp
      simp_rw [ih]
      congr 2
      --simp_rw [ih]
      specialize hf (History_on_turn ini f_law s_law f_strat s_strat t).val (History_on_turn ini f_law s_law f_strat s_strat t).property.1 (by rw [History_on_turn_length] ; exact q) (by rw [History_on_turn_length] ; exact Nat.lt_succ.mp tle)
      convert hf using 1
      congr 2
      · simp_rw [ih]
      · simp_rw [ih]
      · apply heq_prop
      · apply heq_prop
    · rw [dif_neg q, dif_neg q]
      specialize ih (by apply le_trans _ tle ; exact Nat.le.step Nat.le.refl)
      simp_rw [ih]
      congr 2
      --simp_rw [ih]
      specialize hs (History_on_turn ini f_law s_law f_strat s_strat t).val (History_on_turn ini f_law s_law f_strat s_strat t).property.1 (by rw [History_on_turn_length] ; exact q) (by rw [History_on_turn_length] ; exact Nat.lt_succ.mp tle)
      convert hs using 1
      congr 2
      · simp_rw [ih]
      · simp_rw [ih]
      · apply heq_prop
      · apply heq_prop


lemma History_eq_of_strat_strong_eq' (ini : α) (f_law s_law : α → List β → (β → Prop))
  (f_strat F_strat : fStrategy ini f_law s_law)  (s_strat S_strat : sStrategy ini f_law s_law)
  (T : Nat)
  (hf : ∀ hist : List β, (leg : Hist_legal ini f_law s_law hist) → (τ : Turn_fst (List.length hist + 1)) →  hist.length < T → (f_strat hist τ leg).val = (F_strat hist τ leg).val)
  (hs : ∀ hist : List β, (leg : Hist_legal ini f_law s_law hist) → (τ : Turn_snd (List.length hist + 1)) →  hist.length < T → (s_strat hist τ leg).val = (S_strat hist τ leg).val) :
  ∀ t ≤ T, History_on_turn ini f_law s_law f_strat s_strat t = History_on_turn ini f_law s_law F_strat S_strat t :=
  by
  intro t tle
  induction' t with t ih
  · dsimp [History_on_turn]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [dif_pos q, dif_pos q]
      specialize ih (by apply le_trans _ tle ; exact Nat.le.step Nat.le.refl)
      --dsimp
      simp_rw [ih]
      congr 2
      --simp_rw [ih]
      specialize hf (History_on_turn ini f_law s_law f_strat s_strat t).val (History_on_turn ini f_law s_law f_strat s_strat t).property.1 (by rw [History_on_turn_length] ; exact q) (by rw [History_on_turn_length] ; exact Nat.succ_le.mp tle)
      convert hf using 1
      congr 2
      · simp_rw [ih]
      · simp_rw [ih]
      · apply heq_prop
      · apply heq_prop
    · rw [dif_neg q, dif_neg q]
      specialize ih (by apply le_trans _ tle ; exact Nat.le.step Nat.le.refl)
      simp_rw [ih]
      congr 2
      --simp_rw [ih]
      specialize hs (History_on_turn ini f_law s_law f_strat s_strat t).val (History_on_turn ini f_law s_law f_strat s_strat t).property.1 (by rw [History_on_turn_length] ; exact q) (by rw [History_on_turn_length] ; exact Nat.succ_le.mp tle)
      convert hs using 1
      congr 2
      · simp_rw [ih]
      · simp_rw [ih]
      · apply heq_prop
      · apply heq_prop



lemma History_on_turn_suffix
  (ini : α) (f_law s_law : α → List β → (β → Prop))
  (f_strat : fStrategy ini f_law s_law)  (s_strat : sStrategy ini f_law s_law)
  (n m : ℕ) (hmn : m ≤ n) :
  (History_on_turn ini f_law s_law f_strat s_strat m).val <:+ (History_on_turn ini f_law s_law f_strat s_strat n).val :=
  by
  induction' n with n ih
  · rw [Nat.le_zero] at hmn
    rw [hmn]
    dsimp!
    exact List.nil_suffix []
  · rw [Nat.le_iff_lt_or_eq] at hmn
    cases' hmn with hmn hmn
    · rw [Nat.lt_succ] at hmn
      apply List.IsSuffix.trans (ih hmn)
      nth_rewrite 1 [History_on_turn]
      split_ifs with T
      · simp_rw [dif_pos T]
        apply List.suffix_cons
      · simp_rw [dif_neg T]
        apply List.suffix_cons
    · rw [hmn]
      apply List.suffix_rfl




-- # Properties of state


lemma Game_World.state_on_turn_fst_to_snd (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) :
  let h := g.history_on_turn f_strat s_strat turn ;
  (T : Turn_fst (turn + 1)) →
    let T' : Turn_fst (List.length h.val + 1) := (by rw [h.property.2] ; exact T) ;
    g.state_on_turn f_strat s_strat (turn + 1) = g.fst_transition g.init_game_state h (f_strat h.val T' h.property.1)  :=
  by
  intro H tf
  dsimp [H, Game_World.state_on_turn]
  rw [dif_pos tf]

lemma Game_World.state_on_turn_snd_to_fst (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) :
  let h := g.history_on_turn f_strat s_strat turn ;
  (T : Turn_snd (turn + 1)) →
    let T' : Turn_snd (List.length h.val + 1) := (by rw [h.property.2] ; exact T) ;
    g.state_on_turn f_strat s_strat (turn + 1) = g.snd_transition g.init_game_state h (s_strat h.val T' h.property.1)  :=
  by
  intro H tf
  dsimp [H, Game_World.state_on_turn]
  rw [Turn_snd_iff_not_fst] at tf
  rw [dif_neg tf]



-- # Playability


def Game_World.playable (g : Game_World α β) : Prop :=
  ∀ hist : List β, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist →
    ((Turn_fst (List.length hist + 1) → ∃ act : β, g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (List.length hist + 1) → ∃ act : β, g.snd_legal g.init_game_state hist act))

noncomputable
def Game_World.exStrat_fst (g : Game_World α β) (hg : g.playable) : fStrategy g.init_game_state g.fst_legal g.snd_legal :=
  fun hist T leg => Classical.choice <| let ⟨x, xp⟩ := ((hg hist leg).1 T); ⟨(⟨x, xp⟩ : { act // g.fst_legal g.init_game_state hist act })⟩

noncomputable
def Game_World.exStrat_snd (g : Game_World α β) (hg : g.playable) : sStrategy g.init_game_state g.fst_legal g.snd_legal :=
  fun hist T leg => Classical.choice <| let ⟨x, xp⟩ := ((hg hist leg).2 T); ⟨(⟨x, xp⟩ : { act // g.snd_legal g.init_game_state hist act })⟩


lemma Game_World.exStrat_Hist_legal (g : Game_World α β) (hg : g.playable) :
  ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) (g.exStrat_snd hg) t) :=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    apply Hist_legal.nil
  · dsimp [History_on_turn]
    split_ifs with T
    · apply Hist_legal.cons _ _ _ ih
      simp_rw [History_on_turn_length, if_pos T]
      apply ((g.exStrat_fst hg) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) (g.exStrat_snd hg) t).val (by rw [History_on_turn_length] ; exact T) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) (g.exStrat_snd hg) t).property.1).property
    · apply Hist_legal.cons _ _ _ ih
      simp_rw [History_on_turn_length, if_neg T]
      apply ((g.exStrat_snd hg) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) (g.exStrat_snd hg) t).val (by rw [History_on_turn_length] ; exact T) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) (g.exStrat_snd hg) t).property.1).property



lemma Game_World.playable_has_strong_snd_strat (g : Game_World α β) (hg : g.playable) (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) :
  ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat (g.exStrat_snd hg) t) :=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    apply Hist_legal.nil
  · dsimp [History_on_turn]
    split_ifs with T
    · apply Hist_legal.cons _ _ _ ih
      simp_rw [History_on_turn_length, if_pos T]
      apply (f_strat (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat (g.exStrat_snd hg) t).val (by rw [History_on_turn_length] ; exact T) (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat (g.exStrat_snd hg) t).property.1).property
    · apply Hist_legal.cons _ _ _ ih
      simp_rw [History_on_turn_length, if_neg T]
      apply ((g.exStrat_snd hg) (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat (g.exStrat_snd hg) t).val (by rw [History_on_turn_length] ; exact T) (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat (g.exStrat_snd hg) t).property.1).property



lemma Game_World.playable_has_strong_fst (g : Game_World α β) (hg : g.playable) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal ):
  ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) s_strat t) :=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    apply Hist_legal.nil
  · dsimp [History_on_turn]
    split_ifs with T
    · apply Hist_legal.cons _ _ _ ih
      simp_rw [History_on_turn_length, if_pos T]
      apply ((g.exStrat_fst hg) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) s_strat t).val (by rw [History_on_turn_length] ; exact T) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) s_strat t).property.1).property
    · apply Hist_legal.cons _ _ _ ih
      simp_rw [History_on_turn_length, if_neg T]
      apply (s_strat (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) s_strat t).val (by rw [History_on_turn_length] ; exact T) (History_on_turn g.init_game_state g.fst_legal g.snd_legal (g.exStrat_fst hg) s_strat t).property.1).property


def Symm_Game_World.playable (g : Symm_Game_World α β) : Prop := g.toGame_World.playable

noncomputable
def Symm_Game_World.exStrat_fst (g : Symm_Game_World α β) (hg : g.playable) : fStrategy g.init_game_state g.law g.law :=
  g.toGame_World.exStrat_fst hg

noncomputable
def Symm_Game_World.exStrat_snd (g : Symm_Game_World α β) (hg : g.playable) : sStrategy g.init_game_state g.law g.law :=
  g.toGame_World.exStrat_snd hg


lemma Symm_Game_World.exStrat_Hist_legal (g : Symm_Game_World α β) (hg : g.playable) :
  ∀ t, Hist_legal g.init_game_state g.law g.law (History_on_turn g.init_game_state g.law g.law (g.exStrat_fst hg) (g.exStrat_snd hg) t) :=
  by
  apply g.toGame_World.exStrat_Hist_legal


lemma Symm_Game_World.playable_has_strong_snd_strat (g : Symm_Game_World α β) (hg : g.playable) (f_strat : fStrategy g.init_game_state g.law g.law) :
  ∀ t, Hist_legal g.init_game_state g.law g.law (History_on_turn g.init_game_state g.law g.law f_strat (g.exStrat_snd hg) t) :=
  by
  apply g.toGame_World.playable_has_strong_snd_strat

lemma Symm_Game_World.playable_has_strong_fst (g : Symm_Game_World α β) (hg : g.playable) (s_strat : sStrategy g.init_game_state g.law g.law ):
  ∀ t, Hist_legal g.init_game_state g.law g.law (History_on_turn g.init_game_state g.law g.law (g.exStrat_fst hg) s_strat t) :=
  by
  apply g.toGame_World.playable_has_strong_fst


#check Hist_legal_suffix
#check List.rtake
#check List.get

/-
TODO : Show that any legal history can be extended by two strategies
- define strats in mutual block
- for turns less the prescribed hist (:= ph) size, have strat take hist, and if `List.rtake` of hist and ph coincide, play ph acts with `List.get`, else play classical chosen act from g.playable
-
-/
