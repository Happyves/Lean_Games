/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.TurnAPI


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



-- todo   instance Decidable (hist_neutral g [])


open Classical in
def Game_World.hist_on_turn (g : Game_World α β)
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
                -- disjoin on whther win or not
                ⟨ act :: h.val , ⟨Hist_legal.cons h.val act (by rw [if_pos T'] ; exact leg) h.property.1, (by dsimp ; rw [h.property.2])⟩⟩
            else
                let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
                let act := (snd_strat h.val T' h.property.1).val ;
                let leg := (snd_strat h.val T' h.property.1).property ;
                ⟨ act :: h.val , ⟨Hist_legal.cons h.val act (by rw [if_neg ] ; exact leg ; rw [Turn_not_fst_iff_snd] ; exact T') h.property.1, (by dsimp ; rw [h.property.2])⟩⟩


-- def Game_World.hist_on_turn_type (g : Game_World α β)
--   (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy) :
--   Nat → Type _
--   | 0 => {hist : List β // g.hist_legal hist ∧ hist.length = 0}
--   | n+1 => (g.hist_neutral (Game_World.hist_on_turn g fst_strat snd_strat n).val) → {hist : List β // g.hist_legal hist ∧ hist.length = (n+1)}
