/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLibExp.TurnAPI


-- # Game worlds

structure Game_World (α β : Type _) where
  init_game_state : α
  fst_win_states : List β →  Prop
  snd_win_states : List β → Prop
  fst_legal : List β → (β → Prop)
  snd_legal : List β → (β → Prop)
  fst_transition : List β → β → α
  snd_transition : List β → β → α


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






-- # Legality

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

def Game_World.fStrategy (g : Game_World α β) :=
  (hist : List β) → (Turn_fst (hist.length+1)) →
  (g.hist_legal hist) → (g.hist_neutral hist) →
  { act : β // g.fst_legal hist act}

def Game_World.sStrategy (g : Game_World α β) :=
  (hist : List β) → (Turn_snd (hist.length+1)) →
  (g.hist_legal hist) → (g.hist_neutral hist) →
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


inductive Game_World.hist_on_turn_output (g : Game_World α β) (t : Nat) where
| invalid
| terminal (result : {hist : List β // g.hist_legal hist ∧ hist.length = t})
| nonterminal (result : {hist : List β // g.hist_legal hist ∧ hist.length = t}) (property : g.hist_neutral result.val)

def Game_World.hist_on_turn (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) : g.hist_on_turn_output t :=
  match t with
  | 0 =>
      if N : g.hist_neutral []
      then
        .nonterminal ⟨[], ⟨Game_World.hist_legal.nil, rfl⟩⟩ N
      else
        .terminal ⟨[], ⟨Game_World.hist_legal.nil, rfl⟩⟩
  | n+1 =>  let h? := g.hist_on_turn fst_strat snd_strat n
            match h? with
            | .invalid | .terminal _ => .invalid
            | .nonterminal h N =>
            if T : Turn_fst (n+1)
            then
                let T' : Turn_fst (List.length h.val + 1) := by rw [h.property.2] ; exact T ;
                let act := (fst_strat h.val T' h.property.1 N).val ;
                let leg := (fst_strat h.val T' h.property.1 N).property ;
                let H := act :: h.val
                if N : g.hist_neutral H
                then .nonterminal ⟨H , ⟨Game_World.hist_legal.cons h.val act (by rw [if_pos T'] ; exact leg) h.property.1, (by dsimp ; rw [h.property.2])⟩⟩ N
                else .terminal ⟨H , ⟨Game_World.hist_legal.cons h.val act (by rw [if_pos T'] ; exact leg) h.property.1, (by dsimp ; rw [h.property.2])⟩⟩
            else
                let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
                let act := (snd_strat h.val T' h.property.1 N).val ;
                let leg := (snd_strat h.val T' h.property.1 N).property ;
                let H := act :: h.val
                if N : g.hist_neutral H
                then .nonterminal ⟨H , ⟨Game_World.hist_legal.cons h.val act (by rw [if_neg ] ; exact leg ; rw [Turn_not_fst_iff_snd] ; exact T') h.property.1, (by dsimp ; rw [h.property.2])⟩⟩ N
                else .terminal ⟨H , ⟨Game_World.hist_legal.cons h.val act (by rw [if_neg ] ; exact leg ; rw [Turn_not_fst_iff_snd] ; exact T') h.property.1, (by dsimp ; rw [h.property.2])⟩⟩



-- # Games

structure Game (α β : Type u) extends Game_World α β where
  fst_strat : toGame_World.fStrategy
  snd_strat : toGame_World.sStrategy

structure Symm_Game (α β : Type u) extends Symm_Game_World α β where
  fst_strat : toSymm_Game_World.fStrategy
  snd_strat : toSymm_Game_World.sStrategy

def Symm_Game.toGame {α β : Type u} (g : Symm_Game α β) : Game α β :=
 {toGame_World :=  Symm_Game_World.toGame_World (g.toSymm_Game_World)
  fst_strat := g.fst_strat
  snd_strat := g.snd_strat
  }

structure Game_wDraw (α β : Type u) extends Game_World_wDraw α β where
  fst_strat : toGame_World_wDraw.fStrategy
  snd_strat : toGame_World_wDraw.sStrategy


def Game.hist_on_turn (g : Game α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (t : ℕ) : g.hist_on_turn_output t :=
  g.toGame_World.hist_on_turn g.fst_strat g.snd_strat t




-- # State



def Game_World.state_from_hist (g : Game_World α β) : List β → α
| [] => g.init_game_state
| a :: h => if Turn_fst (h.length +1)
            then g.fst_transition h a
            else g.snd_transition h a


inductive Game_World.state_on_turn_output where
| invalid
| valid (state : α)


def Game_World.state_on_turn (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy) (snd_strat : g.sStrategy) : ℕ → Game_World.state_on_turn_output
  | 0 => .valid g.init_game_state
  | n+1 =>  let h := g.hist_on_turn fst_strat snd_strat n
            match h with
            | .invalid => .invalid
            | .terminal _ => .invalid
            | .nonterminal res N =>
                  if T : Turn_fst (n+1)
                  then let T' : Turn_fst (List.length res.val + 1) := by rw [res.property.2] ; exact T ;
                       .valid (g.fst_transition res (fst_strat res.val T' res.property.1 N))
                  else let T' : Turn_snd (List.length res.val + 1) := by rw [Turn_snd_iff_not_fst , res.property.2] ; exact T ;
                       .valid (g.snd_transition res (snd_strat res.val T' res.property.1 N))
