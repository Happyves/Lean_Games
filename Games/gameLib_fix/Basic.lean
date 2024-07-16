/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic

-- should contain game structures, turn manipulations, history and state lemmas


-- # Environments



/--
The game world for state type α and action type β.
-/
structure Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the first player-/
  fst_win_states : α → Prop
  /-- A predicate that decides in which states the game is won for the second player-/
  snd_win_states : α → Prop
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
  transition : α → List β → β → α
  /-- A predicate that decides in which states the game is won for the players-/
  law : α → List β → (β → Prop)

/-- `Symm_Game_World` with addtional drawing states, given by a predicate on states-/
structure Symm_Game_World_wDraw (α β : Type u) extends Symm_Game_World α β where
  draw_states : α → Prop

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


--#exit

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



-- lemma History_on_turn_length {α β : Type u}
--     (ini : α) (fst_strat snd_strat: Strategy α β) (t : Nat) :
--     (History_on_turn ini fst_strat snd_strat t).length = t :=
--   by
--   induction' t with t ih
--   · dsimp [History_on_turn]
--   · dsimp [History_on_turn]
--     split_ifs <;> {rw [List.length_cons, ih]}
