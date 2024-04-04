/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


-- Testing different formalism which might be better for Zermelo, but worries me for PickUpBricks as dependece on initial state is more involved...


import Mathlib.Tactic

structure Symm_Game_World (α β : Type u) where
  /-- Inital state-/
  init_game_state : α
  /-- A predicate that decides in which states the game is won for the players-/
  win_states : α → Prop
  draw_states : α → Prop
  /-- Given  the history, and an action of the player, return next state-/
  transition : List β → β → α
  /-- A predicate that decides in which states the game is won for the players-/
  law : List β → (β → Prop)


def Strategy {α β : Type u} (g : Symm_Game_World α β) := List β → β


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
    (g : Symm_Game_World α β) (fst_strat snd_strat: Strategy g) : ℕ → List β
| 0 => []
| n+1 => let h := History_on_turn g fst_strat snd_strat n
         if Turn_fst (n+1)
         then (fst_strat h) :: h
         else (snd_strat h) :: h

lemma History_on_turn_length {α β : Type u}
    (g : Symm_Game_World α β) (fst_strat snd_strat: Strategy g) (t : Nat) :
    (History_on_turn g fst_strat snd_strat t).length = t :=
  by
  induction' t with t ih
  · dsimp [History_on_turn]
  · dsimp [History_on_turn]
    split_ifs <;> {rw [List.length_cons, ih]}


/--
FIX ME

Given a law that returns a predicate on actions to determine legal actions,
when provided an initial state and a history of actions on which the law may
depend on, we define the notion of a strategy being legal (given another startegy).
A strategy is legal if for all turns, the action for the history on that turn
is legal wrt. the law at that history.
-/
def Strategy_legal_fst {α β : Type u}
  (g : Symm_Game_World α β) (f_law : List β → (β → Prop)) (f_strat s_strat : Strategy g): Prop :=
  ∀ turn : ℕ, Turn_fst (turn + 1) → f_law (History_on_turn g f_strat s_strat turn) (f_strat  (History_on_turn g f_strat s_strat turn))
      -- recall : turn is after the action

/--
FIX ME
-/
def Strategy_legal_snd {α β : Type u}
  (g : Symm_Game_World α β) (s_law : List β → (β → Prop)) (f_strat s_strat : Strategy g): Prop :=
  ∀ turn : ℕ, Turn_snd (turn + 1) → s_law (History_on_turn g f_strat s_strat turn) (s_strat  (History_on_turn g f_strat s_strat turn))
      -- recall : turn is after the action


structure Symm_Game (α β : Type u)  extends Symm_Game_World α β where
  /-- The first players strategy-/
  fst_strat : Strategy toSymm_Game_World
  /-- The second players strategy-/
  snd_strat : Strategy toSymm_Game_World
  /-- The first players strategy is legal wrt. `law` and the second strategy-/
  fst_lawful : Strategy_legal_fst toSymm_Game_World law fst_strat snd_strat
  /-- The second players strategy is legal wrt. `law` and the first strategy-/
  snd_lawful : Strategy_legal_snd toSymm_Game_World law fst_strat snd_strat


def Symm_Game_World.history_on_turn {α β : Type u} (g : Symm_Game_World α β)
    (fst_strat snd_strat: Strategy g) : ℕ → List β :=
    History_on_turn g fst_strat snd_strat


lemma Symm_Game_World.history_on_turn_def {α β : Type u} (g : Symm_Game_World α β):
    g.history_on_turn = History_on_turn g :=
    by
    rfl

def Symm_Game.history_on_turn {α β : Type u} (g : Symm_Game α β) : ℕ → List β :=
  History_on_turn g.toSymm_Game_World g.fst_strat g.snd_strat


lemma Symm_Game.history_on_turn_def {α β : Type u} (g : Symm_Game α β) :
  g.history_on_turn = History_on_turn g.toSymm_Game_World g.fst_strat g.snd_strat :=
  by
  rfl




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


lemma History_on_turn_fst_to_snd (g : Symm_Game_World α β) (fst_strat snd_strat: Strategy g) (turn : ℕ):
  let H := History_on_turn g fst_strat snd_strat ;
  Turn_fst turn → H (turn + 1) = (snd_strat (H turn)) :: (H turn) :=
  by
  intro H tf
  dsimp [H, History_on_turn]
  rw [if_neg ((Turn_fst_not_step turn).mp tf)]

lemma History_on_turn_snd_to_fst (g : Symm_Game_World α β) (fst_strat snd_strat: Strategy g) (turn : ℕ):
  let H := History_on_turn ini fst_strat snd_strat ;
  Turn_snd turn → H (turn + 1) = (fst_strat (H turn)) :: (H turn) :=
  by
  intro H tf
  dsimp [H, History_on_turn]
  rw [if_pos ((Turn_snd_fst_step turn).mp tf)]

lemma Symm_Game_World.history_on_turn_fst_to_snd
  {α β : Type u} (g : Symm_Game_World α β)
  (fst_strat snd_strat: Strategy g) (turn : ℕ):
  let H := g.history_on_turn fst_strat snd_strat ;
  Turn_fst turn → H (turn + 1) = (snd_strat (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game_World.history_on_turn]
  apply History_on_turn_fst_to_snd

lemma Symm_Game_World.history_on_turn_snd_to_fst
  {α β : Type u} (g : Symm_Game_World α β)
  (fst_strat snd_strat: Strategy g) (turn : ℕ):
  let H := g.history_on_turn fst_strat snd_strat ;
  Turn_snd turn → H (turn + 1) = (fst_strat (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game_World.history_on_turn]
  apply History_on_turn_snd_to_fst




lemma Symm_Game.history_on_turn_fst_to_snd
  {α β : Type u} (g : Symm_Game α β) (turn : ℕ):
  let H := g.history_on_turn ;
  Turn_fst turn → H (turn + 1) = (g.snd_strat (H turn)) :: (H turn) :=
  by
  intro H
  dsimp [H, Symm_Game.history_on_turn]
  apply History_on_turn_fst_to_snd

lemma Symm_Game.history_on_turn_snd_to_fst
  {α β : Type u} (g : Symm_Game α β) (turn : ℕ):
  let H := g.history_on_turn ;
  Turn_snd turn → H (turn + 1) = (g.fst_strat (H turn)) :: (H turn) :=
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
  apply @Nat.twoStepInduction (fun t => Turn_fst t → p t) -- use
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
  apply @Nat.twoStepInduction (fun t => Turn_snd t → p t)
  swap
  · intro no
    rw [Turn_snd] at no
    contradiction
  · intro
    exact bh
  · intro n a _ c
    rw [← Turn_snd_step] at c
    exact ih n c (a c)




/--
Given a symmetric game world and strategies, return the state given a turn
-/
def Symm_Game_World.state_on_turn {α β : Type u} (g : Symm_Game_World α β)
    (fst_strat snd_strat: Strategy g) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn fst_strat snd_strat n
         if Turn_fst (n+1)
         then g.transition h (fst_strat h)
         else g.transition h (snd_strat h)


/--
Given a symmetric game world and strategies, return the state given a turn
-/
def Symm_Game.state_on_turn {α β : Type u} (g : Symm_Game α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn n
         if Turn_fst (n+1)
         then g.transition h (g.fst_strat h)
         else g.transition h (g.snd_strat h)



-- # More

lemma Symm_Game_World.mem_History_on_turn {α β : Type u}
    (turn : ℕ)
    (g : Symm_Game_World α β) (f_strat s_strat: Strategy g)
    (x : β) :
    let H := History_on_turn g f_strat s_strat ;
    x ∈ H (turn) ↔ (∃ t < turn, ((Turn_fst (t+1) ∧ x = f_strat (H t)) ∨ (Turn_snd (t+1) ∧ x = s_strat (H t)))) :=
    -- for ↑, recall that `f_strat ini (H t)` is the action of turn `t+1`
    by
    intro H
    apply @Nat.strong_induction_on (fun turn => x ∈ H (turn) ↔ (∃ t < turn, (Turn_fst (t+1) ∧ x = f_strat (H t)) ∨ (Turn_snd (t+1) ∧ x = s_strat (H t)))) turn
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
  (g : Symm_Game_World α β) (f_strat s_strat: Strategy g) {t : ℕ} :
  History_on_turn g f_strat s_strat (t+1) ≠ [] :=
  by
  dsimp [History_on_turn]
  split_ifs <;> decide


lemma History_on_turn_zero
  (g : Symm_Game_World α β) (f_strat s_strat: Strategy g) :
  History_on_turn g f_strat s_strat 0 = [] :=
  by rfl

lemma History_on_turn_getLast_fst_act (g : Symm_Game_World α β) (f_strat s_strat: Strategy g) :
  ∀ t : ℕ, (History_on_turn g f_strat s_strat (t+1)).getLast (by apply History_on_turn_nonempty_of_succ)
    = f_strat [] :=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    simp_rw [if_pos (show Turn_fst (0 + 1) from (by decide))]
    dsimp [List.getLast]
  · dsimp [History_on_turn] at *
    by_cases  q : Turn_fst (Nat.succ t + 1)
    · simp_rw [if_pos q]
      rw [List.getLast_cons]
      · exact ih
    · simp_rw [if_neg q]
      rw [List.getLast_cons]
      · exact ih




inductive Hist_legal (g : Symm_Game_World α β) : List β → Prop
| nil : Hist_legal g []
| cons (l : List β) (act : β) : (if Turn_fst (l.length + 1)
                                then g.law l act
                                else g.law l act) → Hist_legal g l →  Hist_legal g (act :: l)


lemma Symm_Game_World.History_Hist_legal (g : Symm_Game_World α β)
  (f_strat s_strat: Strategy g)
  (fst_lawful : Strategy_legal_fst g g.law f_strat s_strat)
  (snd_lawful : Strategy_legal_snd g g.law f_strat s_strat)
  (t : ℕ) :
  Hist_legal g (History_on_turn g f_strat s_strat t) :=
  by
  induction' t with t ih
  · dsimp [History_on_turn]
    apply Hist_legal.nil
  · dsimp [History_on_turn]
    split_ifs
    all_goals apply Hist_legal.cons _ _ _ ih
    all_goals rename_i c
    all_goals rw [History_on_turn_length]
    · rw [if_pos c]
      exact fst_lawful t c
    · rw [if_neg c]
      exact snd_lawful t c


lemma Symm_Game.History_Hist_legal (g : Symm_Game α β) (t : ℕ) :
  Hist_legal g.toSymm_Game_World  (History_on_turn g.toSymm_Game_World g.fst_strat g.snd_strat t) :=
  by
  apply Symm_Game_World.History_Hist_legal
  · exact g.fst_lawful
  · exact g.snd_lawful




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
