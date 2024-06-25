/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Games.gameLib.Termination


-- Alternative playability for safe hstories


def Symm_Game_World.world_after_fst {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : Symm_Game_World α β := -- act not required to be legal
  {g with init_game_state := g.transition g.init_game_state [] fst_act }


@[simp]
lemma Symm_Game_World.world_after_fst_init {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.transition g.init_game_state [] fst_act :=
  by rfl

@[simp]
lemma Symm_Game_World.world_after_fst_law {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).law = g.law :=
  by rfl


@[simp]
lemma Symm_Game_World.world_after_fst_win_states {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).win_states = g.win_states :=
  by rfl


@[simp]
lemma Symm_Game_World.world_after_fst_transition {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).transition = g.transition :=
  by rfl



-- # Coherent end

def Symm_Game_World.coherent_end_aux
  (g : Symm_Game_World α β) (f_strat s_strat : Strategy α β) (t : ℕ) : Prop :=
  g.win_states (g.state_on_turn f_strat s_strat t) → g.win_states (g.state_on_turn f_strat s_strat (t+1))


def Symm_Game_World.coherent_end (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat : Strategy α β, Strategy_legal_fst g.init_game_state g.law f_strat s_strat →
  Strategy_legal_snd g.init_game_state g.law f_strat s_strat → ∀ t : ℕ, g.coherent_end_aux f_strat s_strat t
  -- ADD LEGALITY IN NON SYMM CONTEXT TOO ??? (only needed by chomp)


lemma Symm_Game_World.coherent_end_all (g : Symm_Game_World α β)  (h : g.coherent_end)
  (f_strat s_strat : Strategy α β) (h₁ : Strategy_legal_fst g.init_game_state g.law f_strat s_strat)
  (h₂ : Strategy_legal_snd g.init_game_state g.law f_strat s_strat) (t n : ℕ) :
  g.win_states (g.state_on_turn f_strat s_strat t) → g.win_states (g.state_on_turn f_strat s_strat (t+n)) :=
  by
  intro H
  induction' n with n ih
  · dsimp
    exact H
  · apply h _ _ h₁ h₂
    exact ih



-- # Playability


/--
Remember that the game goes on even when its over, where players
play dummy values, in our formalism (and coherent end assures certain props)
The ∀ initial states may seem to strong, but its necessary for world_after_fst
and is also explain by playing dummy vals, in a a priori impossible initial state

NOTE : this should be used instead of the inhabited instances for zermelo !!
-/
def law_nonprohibitive (law : α → List β → β → Prop) : Prop :=
  ∀ ini : α, ∀ hist : List β, Hist_legal law law ini hist →  ∃ act : β, law ini hist act

def Symm_Game_World.playable (g : Symm_Game_World α β) : Prop :=
  law_nonprohibitive g.law

lemma Symm_Game_World.playable_has_strat [Inhabited β] (g : Symm_Game_World α β)
  (hg : g.playable) :
  ∃ f_strat : Strategy α β , ∃ s_strat : Strategy α β,
  Strategy_legal_fst g.init_game_state g.law f_strat s_strat ∧
  Strategy_legal_snd g.init_game_state g.law f_strat s_strat :=
  by
  classical -- probably better to have strats that take Hist_leg as input too ?
  use (fun ini hist => if h : Hist_legal g.law g.law ini hist then Classical.choose (hg ini hist h) else default)
  use (fun ini hist => if h : Hist_legal g.law g.law ini hist then Classical.choose (hg ini hist h) else default)
  constructor
  · intro t _
    induction' t with t ih
    · dsimp!
      rw [dif_pos (by apply Hist_legal.nil)]
      apply Classical.choose_spec (hg g.init_game_state [] Hist_legal.nil)
    · unfold History_on_turn
    -- set hist := (History_on_turn g.init_game_state
    -- (fun ini hist => Classical.choose (_ : ∃ act, Symm_Game_World.law g ini hist act))
    -- (fun ini hist => Classical.choose (_ : ∃ act, Symm_Game_World.law g ini hist act)) t)
    -- have pf := Classical.choose_spec (hg g.init_game_state hist)
    -- apply pf
  · intro t _
    set hist := (History_on_turn g.init_game_state
    (fun ini hist => Classical.choose (_ : ∃ act, Symm_Game_World.law g ini hist act))
    (fun ini hist => Classical.choose (_ : ∃ act, Symm_Game_World.law g ini hist act)) t)
    have ps:= Classical.choose_spec (hg g.init_game_state hist)
    apply ps


lemma Symm_Game_World.playable_has_Fst_strat (g : Symm_Game_World α β)
  (hg : g.playable) (s_strat : Strategy α β) :
  ∃ f_strat : Strategy α β,
  Strategy_legal_fst g.init_game_state g.law f_strat s_strat :=
  by
  classical
  use (fun ini hist => Classical.choose (hg ini hist))
  intro t _
  set hist := (History_on_turn g.init_game_state
  (fun ini hist => Classical.choose (_ : ∃ act, Symm_Game_World.law g ini hist act))
  (s_strat) t)
  have pf := Classical.choose_spec (hg g.init_game_state hist)
  apply pf


lemma Symm_Game_World.playable_has_strong_fst_strat (g : Symm_Game_World α β)
  (hg : g.playable) :
  ∃ f_strat : Strategy α β, ∀ (s_strat : Strategy α β),
  Strategy_legal_snd g.init_game_state g.law f_strat s_strat → -- isn't needed ...
  Strategy_legal_fst g.init_game_state g.law f_strat s_strat :=
  by
  classical
  use (fun ini hist => Classical.choose (hg ini hist))
  intro s_strat _
  intro t _
  let hist := History_on_turn g.init_game_state (fun ini hist => Classical.choose (hg ini hist : ∃ act, law g ini hist act)) s_strat t
  have pf := Classical.choose_spec (hg g.init_game_state hist)
  apply pf

lemma Symm_Game_World.playable_has_strong_snd_strat (g : Symm_Game_World α β)
  (hg : g.playable) :
  ∃ s_strat : Strategy α β, ∀ (f_strat : Strategy α β),
  Strategy_legal_fst g.init_game_state g.law f_strat s_strat → -- isn't needed ...
  Strategy_legal_snd g.init_game_state g.law f_strat s_strat :=
  by
  classical
  use (fun ini hist => Classical.choose (hg ini hist))
  intro f_strat _
  intro t _
  let hist := History_on_turn g.init_game_state f_strat (fun ini hist => Classical.choose (hg ini hist : ∃ act, law g ini hist act)) t
  have pf := Classical.choose_spec (hg g.init_game_state hist)
  apply pf



lemma Symm_Game_World.playable_extensible (g : Symm_Game_World α β)
  (hg : g.playable) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act) :
  ∃ f_strat : Strategy α β , ∃ s_strat : Strategy α β,
  Strategy_legal_fst g.init_game_state g.law f_strat s_strat ∧
  Strategy_legal_snd g.init_game_state g.law f_strat s_strat ∧
  f_strat g.init_game_state [] = f_act :=
  by
  classical
  use (fun ini hist => if hist = [] then f_act else Classical.choose (hg ini hist))
  use (fun ini hist => Classical.choose (hg ini hist))
  constructor
  · intro t tf
    cases' t with t
    · dsimp!
      rw [if_pos (by rfl)]
      exact f_act_leg
    · set hist := (History_on_turn g.init_game_state
        (fun ini hist => if hist = [] then f_act else Classical.choose (_ : ∃ act, law g ini hist act))
        (fun ini hist => Classical.choose (_ : ∃ act, law g ini hist act)) (t+1))
      have pf := Classical.choose_spec (hg g.init_game_state hist)
      have beta : ((fun ini hist => if hist = [] then f_act else Classical.choose (hg ini hist)) g.init_game_state hist) = Classical.choose (hg g.init_game_state hist) :=
        by dsimp ; rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
      rw [beta]
      apply pf
  · constructor
    · intro t _
      set hist := (History_on_turn g.init_game_state
        (fun ini hist => if hist = [] then f_act else Classical.choose (_ : ∃ act, law g ini hist act))
        (fun ini hist => Classical.choose (_ : ∃ act, law g ini hist act)) t)
      have ps:= Classical.choose_spec (hg g.init_game_state hist)
      apply ps
    · rw [if_pos (by rfl)]


lemma Symm_Game_World.playable_extensible_fst_strat (g : Symm_Game_World α β)
  (hg : g.playable) (s_strat : Strategy α β)
  (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act) :
  ∃ f_strat : Strategy α β,
  Strategy_legal_fst g.init_game_state g.law f_strat s_strat ∧
  f_strat g.init_game_state [] = f_act :=
  by
  classical
  use (fun ini hist => if hist = [] then f_act else Classical.choose (hg ini hist))
  constructor
  · intro t tf
    cases' t with t
    · dsimp!
      rw [if_pos (by rfl)]
      exact f_act_leg
    · set hist := (History_on_turn g.init_game_state
        (fun ini hist => if hist = [] then f_act else Classical.choose (_ : ∃ act, law g ini hist act)) s_strat
        (Nat.succ t))
      have pf := Classical.choose_spec (hg g.init_game_state hist)
      have beta : ((fun ini hist => if hist = [] then f_act else Classical.choose (hg ini hist)) g.init_game_state hist) = Classical.choose (hg g.init_game_state hist) :=
        by dsimp ; rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
      rw [beta]
      apply pf
  · rw [if_pos (by rfl)]

#exit

-- # Easy termination


inductive Symm_Game_World.has_WL (g : Symm_Game_World α β) : Prop where
| wf : g.is_fst_win → g.has_WL
| ws : g.is_snd_win → g.has_WL


-- lemma Symm_Game_World.has_WL_init_end
--   (g : Symm_Game_World α β)
--   (hg : g.playable)
--   (P : Prop)
--   (hp : P)
--   (h : (P ∧ (¬ g.win_states g.init_game_state)) → g.has_WL) :
--   g.has_WL :=
--   by
--   obtain ⟨fs,ss,_,_⟩ := g.playable_has_strat hg
--   by_cases q2 : g.win_states g.init_game_state
--   · apply Symm_Game_World.has_WL.ws
--     use fs
--     intro _ _ _
--     use 0
--     constructor
--     · decide
--     · constructor
--       · apply q2
--       · intro t no
--         contradiction
--   · exact h ⟨hp, q2⟩





-- # zSymm_Game

structure zSymm_Game_World (α β : Type _) extends Symm_Game_World α β where
  law_careless : careless toSymm_Game_World.law toSymm_Game_World.law toSymm_Game_World.init_game_state toSymm_Game_World.law toSymm_Game_World.transition
  transition_careless : careless toSymm_Game_World.law toSymm_Game_World.law toSymm_Game_World.init_game_state toSymm_Game_World.transition toSymm_Game_World.transition
  coherent : toSymm_Game_World.coherent_end
  playable : toSymm_Game_World.playable



structure zSymm_Game (α β : Type _) extends zSymm_Game_World α β where
  /-- The first players strategy-/
  fst_strat : Strategy α β
  /-- The second players strategy-/
  snd_strat : Strategy α β
  /-- The first players strategy is legal wrt. `law` and the second strategy-/
  fst_lawful : Strategy_legal_fst init_game_state law fst_strat snd_strat
  /-- The second players strategy is legal wrt. `law` and the first strategy-/
  snd_lawful : Strategy_legal_snd init_game_state law fst_strat snd_strat



instance (l : List α): Decidable (l = []) :=
  by
  match l with
  | [] => apply isTrue ; rfl
  | x :: L => apply isFalse ; exact List.cons_ne_nil x L



def fst_strat_deconditioned (s_strat : Strategy α β) (f_act : β) (g : Symm_Game_World α β) : Strategy α β :=
  (fun _ hist => if hist = [] then f_act else s_strat (g.world_after_fst f_act).init_game_state (hist.dropLast))

def snd_strat_deconditioned (f_strat : Strategy α β) (f_act : β) (g : Symm_Game_World α β) : Strategy α β :=
  (fun _ hist => f_strat (g.world_after_fst f_act).init_game_state (hist.dropLast))


lemma Symm_Game_World.History_of_deconditioned
  (g: Symm_Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  History_on_turn g.init_game_state fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) ++ [fst_act] :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [History_on_turn, Turn_fst]
    rw [if_pos (by decide), fst_strat_deconditioned, if_pos (by rfl)]
  · dsimp only [History_on_turn] at *
    by_cases q : Turn_fst (t+1)
    · rw [Turn_fst_not_step] at q
      rw [if_neg q] at *
      rw [← Turn_fst_not_step] at q
      rw [if_pos q, if_pos q] at *
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Symm_Game_World.world_after_fst_init] at ih
      rw [ih]
      rw [snd_strat_deconditioned, List.dropLast_concat]
    · rw [if_neg q, if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q] at *
      rw [fst_strat_deconditioned, snd_strat_deconditioned, if_neg (by apply List.cons_ne_nil)]
      rw [List.cons_append, ← ih]
      congr
      dsimp [snd_strat_deconditioned] at ih
      rw [← Symm_Game_World.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]


def Symm_Game_World.transition_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.transition (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.transition g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Symm_Game_World.transition_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.transition (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.transition g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Symm_Game_World.transition_blind (g : Symm_Game_World α β) : Prop :=
 g.transition_blind_fst ∧ g.transition_blind_snd


def Symm_Game_World.strong_transition_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.transition (g.world_after_fst fst_act).init_game_state hist act
    = g.transition g.init_game_state (hist ++ [fst_act]) act

def Symm_Game_World.strong_transition_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.transition (g.world_after_fst fst_act).init_game_state hist act
    = g.transition g.init_game_state (hist ++ [fst_act]) act


def Symm_Game_World.strong_transition_blind (g : Symm_Game_World α β) : Prop :=
 g.strong_transition_blind_fst ∧ g.strong_transition_blind_snd

lemma Symm_Game_World.strong_transition_blind_toWeak (g : Symm_Game_World α β) :
  g.strong_transition_blind → g.transition_blind :=
  by
  rintro ⟨f_strong, s_strong⟩
  constructor
  · intro f_strat s_strat f_act f_act_leg fst_strat snd_strat t act
    rw [Symm_Game_World.History_of_deconditioned]
    apply f_strong
    exact f_act_leg
  · intro f_strat s_strat f_act f_act_leg fst_strat snd_strat t act
    rw [Symm_Game_World.History_of_deconditioned]
    apply s_strong
    exact f_act_leg


def Symm_Game_World.world_after_preHist {α β : Type u} (g : Symm_Game_World α β)
  (prehist : List β) : Symm_Game_World α β := -- act not required to be legal
  match prehist with
  | [] => g
  | last :: L => {g with init_game_state := g.transition g.init_game_state L last}


lemma Symm_Game_World.world_after_preHist_win_states {α β : Type u} (g : Symm_Game_World α β)
  (prehist : List β) : (g.world_after_preHist prehist).win_states = g.win_states :=
  by cases' prehist <;> rfl



def Symm_Game_World.hyper_transition_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.law g.law g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.transition (g.world_after_preHist prehist).init_game_state hist act
    = g.transition g.init_game_state (hist ++ prehist) act

def Symm_Game_World.hyper_transition_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.law g.law g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.transition (g.world_after_preHist prehist).init_game_state hist act
    = g.transition g.init_game_state (hist ++ prehist) act


def Symm_Game_World.hyper_transition_blind (g : Symm_Game_World α β) : Prop :=
 g.hyper_transition_blind_fst ∧ g.hyper_transition_blind_snd


lemma Symm_Game_World.hyper_transition_blind_transition_eq (g : Symm_Game_World α β) :
  g.hyper_transition_blind → (g.transition g.init_game_state = g.transition g.init_game_state) :=
  by
  intro h
  have := h.2 [] (by apply Hist_legal.nil)
  dsimp [Symm_Game_World.world_after_preHist] at this
  simp_rw [List.append_nil] at this
  rfl


lemma Symm_Game_World.hyper_transition_blind_toStrong (g : Symm_Game_World α β) :
  g.hyper_transition_blind → g.strong_transition_blind :=
  by
  rintro ⟨f_hyper, s_hyper⟩
  constructor
  · intro f_act f_leg hist act
    specialize f_hyper [f_act] _ hist act
    · apply Hist_legal.cons
      · dsimp
        rw [if_pos (by decide)]
        exact f_leg
      · apply Hist_legal.nil
    · dsimp [Symm_Game_World.world_after_fst, Symm_Game_World.world_after_preHist] at *
      exact f_hyper
  · intro f_act f_leg hist act
    specialize s_hyper [f_act] _ hist act
    · apply Hist_legal.cons
      · dsimp
        rw [if_pos (by decide)]
        exact f_leg
      · apply Hist_legal.nil
    · dsimp [Symm_Game_World.world_after_fst, Symm_Game_World.world_after_preHist] at *
      exact s_hyper

@[simp]
lemma Symm_Game_World.world_after_preHist_singleton {α β : Type u} (g : Symm_Game_World α β)
  (act : β) : g.world_after_preHist [act] = g.world_after_fst act :=
  by
  dsimp [Symm_Game_World.world_after_fst, Symm_Game_World.world_after_preHist]


lemma zSymm_Game_World.is_hyper_transition_blind (g : zSymm_Game_World α β) :
  g.toSymm_Game_World.hyper_transition_blind :=
  by
  constructor
  · intro prehist preh_leg hist act
    have := g.transition_careless g.init_game_state hist prehist
    match prehist with
    | [] =>
        dsimp [Symm_Game_World.world_after_preHist]
        rw [List.append_nil]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this]
        · dsimp [Symm_Game_World.world_after_preHist]
        · exact preh_leg
  · intro prehist preh_leg hist act
    have := g.transition_careless g.init_game_state hist prehist
    match prehist with
    | [] =>
        dsimp [Symm_Game_World.world_after_preHist]
        rw [List.append_nil]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this]
        · dsimp [Symm_Game_World.world_after_preHist]
        · exact preh_leg




lemma Symm_Game_World.State_of_deconditioned
  (g: Symm_Game_World α β)
  (tb : g.transition_blind)
  (fst_act: β)
  (fst_act_legal: g.law g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  g.state_on_turn fst_strat snd_strat (turn + 1) =
  (g.world_after_fst fst_act).state_on_turn f_strat s_strat turn :=
  by
  intro fst_strat snd_strat
  cases' turn with t
  · dsimp [state_on_turn]
    rw [if_pos (by decide)]
    dsimp [history_on_turn, History_on_turn]
    rw [fst_strat_deconditioned, if_pos (by rfl)]
  · dsimp [state_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q]
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      dsimp [history_on_turn]
      have := g.History_of_deconditioned fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [snd_strat_deconditioned, List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.2 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (f_strat (world_after_fst g fst_act).init_game_state (History_on_turn (world_after_fst g fst_act).init_game_state f_strat s_strat t))
      rw [← Symm_Game_World.world_after_fst_init]
      rw [← this]
      clear this
      rfl
    · rw [Turn_not_fst_iff_snd, Turn_snd_fst_step] at q
      rw [if_pos q]
      dsimp [history_on_turn]
      rw [← Turn_fst_step, Turn_fst_not_step] at q
      rw [if_neg q]
      rw [fst_strat_deconditioned, if_neg (by apply History_on_turn_nonempty_of_succ)]
      have := g.History_of_deconditioned fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.1 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (s_strat (world_after_fst g fst_act).init_game_state (History_on_turn (Symm_Game_World.transition g g.init_game_state [] fst_act) f_strat s_strat t))
      rw [← Symm_Game_World.world_after_fst_init] at this
      rw [← Symm_Game_World.world_after_fst_init]
      rw [← this]


lemma zSymm_Game_World.State_of_deconditioned
  (g: zSymm_Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.law g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned s_strat fst_act g.toSymm_Game_World
  let snd_strat := snd_strat_deconditioned f_strat fst_act g.toSymm_Game_World
  g.state_on_turn fst_strat snd_strat (turn + 1) =
  (g.world_after_fst fst_act).state_on_turn f_strat s_strat turn :=
  by
  apply Symm_Game_World.State_of_deconditioned
  · apply Symm_Game_World.strong_transition_blind_toWeak
    apply Symm_Game_World.hyper_transition_blind_toStrong
    apply zSymm_Game_World.is_hyper_transition_blind
  · exact fst_act_legal







-- -- # Careless strat


-- def Game_World.Strategy_blind_fst (strat : Strategy α β) (g : Game_World α β) : Prop :=
--   ∀ s_strat: Strategy α β,
--   let fst_act := strat g.init_game_state []
--   ∀ turn : ℕ, strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state s_strat strat turn)
--     = strat g.init_game_state (History_on_turn g.init_game_state strat s_strat (turn + 1))


-- def Game_World.Strategy_blind_snd (strat : Strategy α β) (g : Game_World α β) : Prop :=
--   ∀ f_strat: Strategy α β,
--   let fst_act := f_strat g.init_game_state []
--   ∀ turn : ℕ, strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state strat f_strat turn)
--     = strat g.init_game_state (History_on_turn g.init_game_state f_strat strat (turn + 1))

-- def Game_World.Strategy_blind (strat : Strategy α β) (g : Game_World α β) : Prop :=
--   g.Strategy_blind_fst strat ∧ g.Strategy_blind_snd strat

-- def Game_World.strong_Strategy_blind (strat : Strategy α β) (g : Game_World α β) : Prop :=
--   ∀ fst_act : β, g.law g.init_game_state [] fst_act →
--   ∀ hist : List β, strat (g.world_after_fst fst_act).init_game_state hist
--     = strat g.init_game_state (hist ++ [fst_act])

-- lemma Game_World.world_after_fst_History_blind (g : Game_World α β)
--   (f_strat s_strat : Strategy α β) (turn : ℕ)
--   (hf : g.Strategy_blind_fst f_strat) (hs : g.Strategy_blind_snd s_strat)
--   :
--   (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn)
--   ++ [(f_strat g.init_game_state [])] = History_on_turn g.init_game_state f_strat s_strat (turn+1) :=
--   by
--   rw [History_on_turn]
--   induction' turn with t ih
--   · dsimp [History_on_turn]
--     rw [if_pos (by decide)]
--   · dsimp [History_on_turn]
--     by_cases q : Turn_fst (t+1)
--     · rw [if_pos q] at *
--       rw [Turn_fst_not_step] at q
--       rw [if_neg q]
--       rw [← Turn_fst_not_step] at q
--       rw [if_pos q]
--       rw [Game_World.world_after_fst_init] at *
--       rw [List.cons_append, ih]
--       congr 1
--       have := hs f_strat t
--       rw [← Game_World.world_after_fst_init, this]
--       dsimp [History_on_turn]
--       rw [if_pos q]
--     · rw [if_neg q] at *
--       rw [Turn_fst_not_step, not_not] at q
--       rw [if_pos q]
--       rw [← @not_not (Turn_fst (t + 1 + 1)), ← Turn_fst_not_step] at q
--       rw [if_neg q]
--       rw [Game_World.world_after_fst_init] at *
--       rw [List.cons_append]
--       congr 1
--       have := hf s_strat t
--       rw [Game_World.world_after_fst_init] at this
--       rw [this]
--       dsimp [History_on_turn]
--       rw [if_neg q]


-- lemma Game_World.world_after_fst_History_strong_blind (g : Game_World α β)
--   (f_strat s_strat : Strategy α β) (turn : ℕ)
--   (f_leg : Strategy_legal_fst g.init_game_state g.law f_strat s_strat)
--   (hf : g.strong_Strategy_blind f_strat) (hs : g.strong_Strategy_blind s_strat)
--   :
--   (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn)
--   ++ [(f_strat g.init_game_state [])] = History_on_turn g.init_game_state f_strat s_strat (turn+1) :=
--   by
--   rw [History_on_turn]
--   induction' turn with t ih
--   · dsimp [History_on_turn]
--     rw [if_pos (by decide)]
--   · unfold History_on_turn
--     by_cases q : Turn_fst (t+1)
--     · rw [if_pos q]
--       rw [List.cons_append, ih]
--       specialize hs (f_strat g.init_game_state []) (by apply f_leg 0 (by decide)) (History_on_turn (Game_World.transition g g.init_game_state [] (f_strat g.init_game_state [])) s_strat f_strat t)
--       rw [← Game_World.world_after_fst_init] at hs
--       rw [hs, ih]
--       rw [if_neg (show ¬ Turn_fst (Nat.succ t + 1) from (by rw [← Turn_fst_not_step]; exact q))]
--     · rw [if_neg q]
--       rw [List.cons_append, ih]
--       specialize hf (f_strat g.init_game_state []) (by apply f_leg 0 (by decide)) (History_on_turn (Game_World.transition g g.init_game_state [] (f_strat g.init_game_state [])) s_strat f_strat t)
--       rw [← Game_World.world_after_fst_init] at hf
--       rw [hf, ih]
--       rw [if_pos (show Turn_fst (Nat.succ t + 1) from (by rw [iff_not_comm.mp (Turn_fst_not_step (t+1))]; exact q))]


-- -- might not be the case, because we have no carelessness of other strat
-- -- lemma Game_World.strong_Strategy_blind_toWeak (strat : Strategy α β) (g : Game_World α β)
-- --   (f_leg : Strategy_legal_fst g.init_game_state g.law strat s_strat) :
-- --   g.strong_Strategy_blind strat → g.Strategy_blind strat :=
-- --   by
-- --   intro hyp
-- --   constructor
-- --   · intro s_strat f_act t
-- --     rw [hyp]



-- --#exit

-- def Game_World.hyper_Strategy_blind
--   (strat : Strategy α β) (g : Game_World α β) : Prop :=
--   ∀ prehist : List β, Hist_legal g.law g.law g.init_game_state prehist →
--   ∀ hist : List β, strat (g.world_after_preHist prehist).init_game_state hist
--     = strat g.init_game_state (hist ++ prehist)


-- lemma Game_World.hyper_Strategy_blind_toStrong
--   (strat : Strategy α β) (g : Game_World α β) :
--   g.hyper_Strategy_blind strat → g.strong_Strategy_blind strat :=
--   by
--   intro hyp
--   intro f_act f_leg hist
--   specialize hyp [f_act] _ hist
--   · apply Hist_legal.cons
--     · dsimp
--       rw [if_pos (by decide)]
--       exact f_leg
--     · apply Hist_legal.nil
--   · dsimp [Game_World.world_after_fst, Game_World.world_after_preHist] at *
--     exact hyp


--#exit

-- # Blind law

def Symm_Game_World.legal_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.law (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.law g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Symm_Game_World.legal_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  ∀ turn : ℕ, ∀ act : β, g.law (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.law g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Symm_Game_World.legal_blind (g : Symm_Game_World α β) : Prop :=
 g.legal_blind_fst ∧ g.legal_blind_snd


def Symm_Game_World.strong_legal_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.law (g.world_after_fst fst_act).init_game_state hist act
    = g.law g.init_game_state (hist ++ [fst_act]) act

def Symm_Game_World.strong_legal_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ fst_act : β, g.law g.init_game_state [] fst_act →
  ∀ hist : List β, ∀ act : β, g.law (g.world_after_fst fst_act).init_game_state hist act
    = g.law g.init_game_state (hist ++ [fst_act]) act


def Symm_Game_World.strong_legal_blind (g : Symm_Game_World α β) : Prop :=
 g.strong_legal_blind_fst ∧ g.strong_legal_blind_snd

lemma Symm_Game_World.strong_legal_blind_toWeak (g : Symm_Game_World α β) :
  g.strong_legal_blind → g.legal_blind :=
  by
  rintro ⟨f_strong, s_strong⟩
  constructor
  · intro f_strat s_strat f_act f_act_leg fst_strat snd_strat t act
    rw [Symm_Game_World.History_of_deconditioned]
    apply f_strong
    exact f_act_leg
  · intro f_strat s_strat f_act f_act_leg fst_strat snd_strat t act
    rw [Symm_Game_World.History_of_deconditioned]
    apply s_strong
    exact f_act_leg




def Symm_Game_World.hyper_legal_blind_fst (g : Symm_Game_World α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.law g.law g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.law (g.world_after_preHist prehist).init_game_state hist act
    = g.law g.init_game_state (hist ++ prehist) act

def Symm_Game_World.hyper_legal_blind_snd (g : Symm_Game_World α β) : Prop :=
  ∀ prehist : List β, Hist_legal g.law g.law g.init_game_state prehist →
  ∀ hist : List β, ∀ act : β, g.law (g.world_after_preHist prehist).init_game_state hist act
    = g.law g.init_game_state (hist ++ prehist) act


def Symm_Game_World.hyper_legal_blind (g : Symm_Game_World α β) : Prop :=
 g.hyper_legal_blind_fst ∧ g.hyper_legal_blind_snd


lemma Symm_Game_World.hyper_legal_blind_legal_eq (g : Symm_Game_World α β) :
  g.hyper_legal_blind → (g.law g.init_game_state = g.law g.init_game_state) :=
  by
  intro h
  have := h.2 [] (by apply Hist_legal.nil)
  dsimp [Symm_Game_World.world_after_preHist] at this
  simp_rw [List.append_nil] at this
  rfl


lemma Symm_Game_World.hyper_legal_blind_toStrong (g : Symm_Game_World α β) :
  g.hyper_legal_blind → g.strong_legal_blind :=
  by
  rintro ⟨f_hyper, s_hyper⟩
  constructor
  · intro f_act f_leg hist act
    specialize f_hyper [f_act] _ hist act
    · apply Hist_legal.cons
      · dsimp
        rw [if_pos (by decide)]
        exact f_leg
      · apply Hist_legal.nil
    · dsimp [Symm_Game_World.world_after_fst, Symm_Game_World.world_after_preHist] at *
      exact f_hyper
  · intro f_act f_leg hist act
    specialize s_hyper [f_act] _ hist act
    · apply Hist_legal.cons
      · dsimp
        rw [if_pos (by decide)]
        exact f_leg
      · apply Hist_legal.nil
    · dsimp [Symm_Game_World.world_after_fst, Symm_Game_World.world_after_preHist] at *
      exact s_hyper


lemma zSymm_Game_World.is_hyper_legal_blind (g : zSymm_Game_World α β) :
  g.toSymm_Game_World.hyper_legal_blind :=
  by
  constructor
  · intro prehist preh_leg hist act
    have := g.law_careless g.init_game_state hist prehist
    match prehist with
    | [] =>
        dsimp [Symm_Game_World.world_after_preHist]
        rw [List.append_nil]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this]
        · dsimp [Symm_Game_World.world_after_preHist]
        · exact preh_leg
  · intro prehist preh_leg hist act
    have := g.law_careless g.init_game_state hist prehist
    match prehist with
    | [] =>
        dsimp [Symm_Game_World.world_after_preHist]
        rw [List.append_nil]
    | x :: l =>
        specialize this (by apply List.noConfusion)
        rw [this]
        · dsimp [Symm_Game_World.world_after_preHist]
        · exact preh_leg


lemma Symm_Game_World.law_deconditioned_fst
  (g: Symm_Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.law g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (s_leg: Strategy_legal_snd (g.world_after_fst fst_act).init_game_state (g.world_after_fst fst_act).law f_strat s_strat)
  (b : g.legal_blind_fst)
  :
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  Strategy_legal_fst g.init_game_state g.law fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · dsimp [History_on_turn, fst_strat_deconditioned]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · rw [← b, Symm_Game_World.History_of_deconditioned]
    · dsimp [History_on_turn, fst_strat_deconditioned]
      rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil fst_act [])]
      rw [List.dropLast_concat]
      apply s_leg
      rw [Turn_snd_fst_step]
      exact tf
    · exact fst_act_legal


lemma Symm_Game_World.law_deconditioned_snd
  (g: Symm_Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.law g.init_game_state [] fst_act)
  (f_strat s_strat : Strategy α β)
  (f_leg: Strategy_legal_fst (g.world_after_fst fst_act).init_game_state (g.world_after_fst fst_act).law f_strat s_strat)
  (b : g.legal_blind_snd)
  :
  let fst_strat := fst_strat_deconditioned s_strat fst_act g
  let snd_strat := snd_strat_deconditioned f_strat fst_act g
  Strategy_legal_snd g.init_game_state g.law fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · contradiction
  · rw [← b, Symm_Game_World.History_of_deconditioned]
    · dsimp [History_on_turn, snd_strat_deconditioned]
      rw [List.dropLast_concat]
      apply f_leg
      rw [Turn_fst_snd_step]
      exact tf
    · exact fst_act_legal



def zSymm_Game_World.world_after_fst {α β : Type u} (g : zSymm_Game_World α β)
  (fst_act : β) (fst_act_legal: g.law g.init_game_state [] fst_act) : zSymm_Game_World α β :=
  {(g.toSymm_Game_World.world_after_fst fst_act) with
      law_careless := by dsimp ; apply g.law_careless
      transition_careless := by dsimp ; apply g.transition_careless
      coherent := by
                  intro f_strat s_strat f_leg s_leg t
                  intro fws
                  dsimp at *
                  have := g.State_of_deconditioned fst_act fst_act_legal f_strat s_strat
                  dsimp [Symm_Game_World.world_after_fst] at this
                  rw [← this] at *
                  clear this
                  have := (g.coherent (fst_strat_deconditioned s_strat fst_act g.toSymm_Game_World) (snd_strat_deconditioned f_strat fst_act g.toSymm_Game_World)
                      (by apply g.law_deconditioned_fst fst_act fst_act_legal _ _ s_leg  (g.strong_legal_blind_toWeak (g.hyper_legal_blind_toStrong g.is_hyper_legal_blind)).1)
                      (by apply g.law_deconditioned_snd fst_act fst_act_legal _ _ f_leg  (g.strong_legal_blind_toWeak (g.hyper_legal_blind_toStrong g.is_hyper_legal_blind)).2)
                      (t+1))
                  exact this fws
      playable := by apply g.playable
                  }



lemma zSymm_Game_World.world_after_fst_init (g : zSymm_Game_World α β)
  (fst_act : β) (fst_act_legal: g.law g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).init_game_state = g.transition g.init_game_state [] fst_act :=
  by
  rfl


@[simp]
lemma zSymm_Game_World.world_after_fst_law {α β : Type u} (g : zSymm_Game_World α β)
  (fst_act : β) (fst_act_legal: g.law g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).law = g.law :=
  by rfl


@[simp]
lemma zSymm_Game_World.world_after_fst_win_states {α β : Type u} (g : zSymm_Game_World α β)
  (fst_act : β) (fst_act_legal: g.law g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).win_states = g.win_states :=
  by rfl



@[simp]
lemma zSymm_Game_World.world_after_fst_transition {α β : Type u} (g : zSymm_Game_World α β)
  (fst_act : β) (fst_act_legal: g.law g.init_game_state [] fst_act) :
  (g.world_after_fst fst_act fst_act_legal).transition = g.transition :=
  by rfl





def zSymm_Game.history_on_turn {α β : Type u} (g : zSymm_Game α β) : ℕ → List β :=
  History_on_turn g.init_game_state g.fst_strat g.snd_strat


def zSymm_Game.state_on_turn {α β : Type u} (g : zSymm_Game α β) : ℕ → α
| 0 => g.init_game_state
| n+1 => let h := g.history_on_turn n
         if Turn_fst (n+1)
         then g.transition g.init_game_state h (g.fst_strat g.init_game_state h)
         else g.transition g.init_game_state h (g.snd_strat g.init_game_state h)




-- # Termination



def zSymm_Game.fst_win  {α β : Type _} (g : zSymm_Game α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn ∧ g.win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral g.fst_strat g.snd_strat t)


def zSymm_Game.snd_win  {α β : Type u} (g : zSymm_Game α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral g.fst_strat g.snd_strat t)



def zSymm_Game_World.is_fst_win  {α β : Type u} (g : zSymm_Game_World α β) : Prop :=
  ∃ ws : Strategy α β, --g.Strategy_blind_fst ws ∧
  ∀ snd_s : Strategy α β, --g.Strategy_blind_fst snd_s →
   (snd_leg : Strategy_legal_snd g.init_game_state g.law ws snd_s) →
   ∃ (ws_leg : Strategy_legal_fst g.init_game_state g.law ws snd_s),
  ({g with fst_strat := ws, fst_lawful := ws_leg, snd_strat := snd_s, snd_lawful := snd_leg} : Symm_Game α β).fst_win


def zSymm_Game_World.is_snd_win  {α β : Type u} (g : zSymm_Game_World α β) : Prop :=
  ∃ ws : Strategy α β, -- g.Strategy_blind_snd ws ∧
  ∀ fst_s : Strategy α β, --g.Strategy_blind_snd fst_s →
   (fst_leg : Strategy_legal_fst g.init_game_state g.law fst_s ws) →
   ∃ (ws_leg : Strategy_legal_snd g.init_game_state g.law fst_s ws),
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Symm_Game α β).snd_win



inductive zSymm_Game_World.has_WL (g : zSymm_Game_World α β) : Prop where
| wf : g.is_fst_win → g.has_WL
| ws : g.is_snd_win → g.has_WL


lemma zSymm_Game_World.has_WL_init_end
  (g : zSymm_Game_World α β)
  (P : Prop)
  (hp : P)
  (h : (P ∧ (¬ g.win_states g.init_game_state)) → g.has_WL) :
  g.has_WL :=
  by
  obtain ⟨ss,ss_prop⟩ := g.playable_has_strong_snd_strat g.playable
  by_cases q2 : g.win_states g.init_game_state
  · apply zSymm_Game_World.has_WL.ws
    use ss
    intro fs fs_leg
    constructor
    · use 0
      constructor
      · decide
      · constructor
        · apply q2
        · intro t no
          contradiction
    · exact ss_prop fs fs_leg
  · exact h ⟨hp, q2⟩





-- # More conditioining

def zSymm_Game_World.snd_strat_conditioned (f_strat : Strategy α β) (f_act : β) (g : zSymm_Game_World α β) : Strategy α β :=
  fun _ hist => f_strat g.init_game_state (hist ++ [f_act])

open Classical

noncomputable
def zSymm_Game_World.fst_strat_conditioned [Inhabited β] (g : zSymm_Game_World α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  : Strategy α β :=
  fun (_ : α) hist  =>
    if hh : hist = [] -- shouldn't happen, as snd strat
    then default -- dummy
    else let f_act := List.getLast hist hh
         if H : g.law g.init_game_state [] f_act-- should be the cases ?!?
         then (f_strat hist hh H) (g.transition g.init_game_state [] f_act) hist.dropLast -- is it ? since ref to history in current game
         else default


lemma zSymm_Game_World.fst_strat_conditioned_get_rw_to_work [Inhabited β] (g : zSymm_Game_World α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β) :
  g.fst_strat_conditioned f_strat =
  fun (_ : α) hist  =>
    if hh : hist = [] -- shouldn't happen, as snd strat
    then default -- dummy
    else let f_act := List.getLast hist hh
         if H : g.law g.init_game_state [] f_act-- should be the cases ?!?
         then (f_strat hist hh H) (g.transition g.init_game_state [] f_act) hist.dropLast -- is it ? since ref to history in current game
         else default
  :=
  by
  rfl




lemma zSymm_Game_World.history_on_turn_conditioned
  [Inhabited β] (g : zSymm_Game_World α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.law g.init_game_state [] (h.getLast hne)) → (Hl : g.law g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.law g.init_game_state [] (fst_s g.init_game_state [])):
  let f_act := fst_s g.init_game_state []
  ∀ t : ℕ,
  g.history_on_turn fst_s (g.fst_strat_conditioned f_strat) (t+1) =
  ((g.world_after_fst f_act f_act_leg).history_on_turn (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) t) ++ [f_act]:=
  by
  intro f_act t
  induction' t with t ih
  · dsimp [Symm_Game_World.history_on_turn, History_on_turn]
    rw [if_pos (by decide)]
  · dsimp [Symm_Game_World.history_on_turn, History_on_turn]
    by_cases q : Turn_fst (Nat.succ t + 1)
    · rw [if_pos q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at q
      rw [if_neg q,if_neg q]
      dsimp [zSymm_Game_World.snd_strat_conditioned]
      unfold Symm_Game_World.history_on_turn at ih
      rw [← ih]
      dsimp [History_on_turn]
      rw [if_neg q]
    · rw [if_neg q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at q
      rw [if_pos q, if_pos q]
      dsimp [zSymm_Game_World.fst_strat_conditioned]
      rw [dif_neg (by apply List.cons_ne_nil)]
      have := History_on_turn_getLast_fst_act g.init_game_state fst_s (g.fst_strat_conditioned f_strat) (t)
      dsimp [History_on_turn] at this
      simp_rw [if_pos q] at this
      rw [dif_pos (by rw [this] ; apply f_act_leg)]
      unfold Symm_Game_World.history_on_turn at ih
      rw [← ih]
      have that : History_on_turn g.init_game_state fst_s (fst_strat_conditioned g f_strat) (t + 1) =
                  (fst_s g.init_game_state (History_on_turn g.init_game_state fst_s (fst_strat_conditioned g f_strat) t) ::
                   History_on_turn g.init_game_state fst_s (fst_strat_conditioned g f_strat) t) :=
        by
        dsimp [History_on_turn]
        rw [if_pos q]
      have thut : List.getLast (History_on_turn g.init_game_state fst_s (g.fst_strat_conditioned f_strat) (t + 1))  (by apply History_on_turn_nonempty_of_succ) = f_act :=
        by
        simp_rw [ih]
        rw [List.getLast_append]
      simp_rw [← that]
      specialize h_f_strat (History_on_turn g.init_game_state fst_s (g.fst_strat_conditioned f_strat) (t + 1)) [f_act]
                  (by apply History_on_turn_nonempty_of_succ) (by apply List.cons_ne_nil)
                  (by rw [thut] ; apply f_act_leg) (by apply f_act_leg)
                  (by apply thut)
      rw [h_f_strat]
      congr
      rw [ih]
      rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)]
      dsimp
      rw [List.append_nil]





lemma zSymm_Game_World.state_on_turn_conditioned
  [Inhabited β] (g : zSymm_Game_World α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.law g.init_game_state [] (h.getLast hne)) → (Hl : g.law g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.law g.init_game_state [] (fst_s g.init_game_state [])):
  let f_act := fst_s g.init_game_state []
  ∀ t : ℕ,
  g.state_on_turn fst_s (g.fst_strat_conditioned f_strat) (t+1) =
  (g.world_after_fst f_act f_act_leg).state_on_turn (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) t:=
  by
  intro f_act t
  cases' t with t
  · dsimp [Symm_Game_World.state_on_turn]
    rw [if_pos (by decide)]
    dsimp [Symm_Game_World.history_on_turn, History_on_turn, zSymm_Game_World.world_after_fst_init]
  · dsimp [Symm_Game_World.state_on_turn]
    by_cases q : Turn_fst (t + 1 + 1)
    · rw [if_pos q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at q
      rw [if_neg q]
      rw [g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg]
      have := careless_singleton _ _ _ _ _ (g.transition_careless)
      specialize this g.init_game_state ((Symm_Game_World.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toSymm_Game_World
          (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
          (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t)) f_act f_act_leg
      simp_rw [this]
      congr
    · rw [if_neg q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at q
      rw [if_pos q]
      rw [g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg]
      have := careless_singleton _ _ _ _ _ (g.transition_careless)
      specialize this g.init_game_state ((Symm_Game_World.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toSymm_Game_World
          (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
          (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t)) f_act f_act_leg
      simp_rw [this]
      congr
      dsimp [fst_strat_conditioned]
      rw [dif_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)]
      rw [dif_pos (by rw [List.getLast_append] ; apply f_act_leg)]
      rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)]
      dsimp
      rw [List.append_nil]
      have := h_f_strat ((Symm_Game_World.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toSymm_Game_World
            (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
            (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t ++
             [fst_s g.init_game_state []])) [f_act]
             (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)
             (by apply List.cons_ne_nil)
             (by rw [List.getLast_append] ; apply f_act_leg)
             (by apply f_act_leg)
             (by rw [List.getLast_append] ; dsimp)
      rw [this]
      rw [List.getLast_append]
      rfl



lemma zSymm_Game_World.conditioned_legal_fst
  [Inhabited β] (g : zSymm_Game_World α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.law g.init_game_state [] (h.getLast hne)) → (Hl : g.law g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.law g.init_game_state [] (fst_s g.init_game_state [])) :
  let f_act := fst_s g.init_game_state []
  Strategy_legal_fst g.init_game_state g.law fst_s (g.fst_strat_conditioned f_strat)
  ↔ Strategy_legal_snd (g.world_after_fst f_act f_act_leg).init_game_state (g.world_after_fst f_act f_act_leg).law (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) :=
  by
  intro f_act
  constructor
  · intro leg t ts
    have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
    have hc := careless_singleton _ _ _ _ _ (g.law_careless)
    specialize leg (t+1) (by rw [← Turn_snd_fst_step] ; exact ts)
    unfold Symm_Game_World.history_on_turn at hh
    rw [hh] at leg
    rw [hc] at leg
    · dsimp [snd_strat_conditioned]
      apply leg
    · apply f_act_leg
  · intro leg t tf
    cases' t with t
    · dsimp [History_on_turn]
      apply f_act_leg
    · specialize leg (t) (by rw [Turn_snd_fst_step] ; exact tf)
      have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
      have hc := careless_singleton _ _ _ _ _ (g.law_careless)
      unfold Symm_Game_World.history_on_turn at hh
      rw [hh, hc]
      · dsimp [snd_strat_conditioned] at leg
        apply leg
      · apply f_act_leg




lemma zSymm_Game_World.conditioned_legal_snd
  [Inhabited β] (g : zSymm_Game_World α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.law g.init_game_state [] (h.getLast hne)) → (Hl : g.law g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.law g.init_game_state [] (fst_s g.init_game_state [])) :
  let f_act := fst_s g.init_game_state []
  Strategy_legal_snd g.init_game_state g.law fst_s (g.fst_strat_conditioned f_strat)
  ↔ Strategy_legal_fst (g.world_after_fst f_act f_act_leg).init_game_state (g.world_after_fst f_act f_act_leg).law (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) :=
  by
  intro f_act
  constructor
  · intro leg t tf
    have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
    have hc := careless_singleton _ _ _ _ _ (g.law_careless)
    specialize leg (t+1) (by rw [← Turn_fst_snd_step] ; exact tf)
    unfold Symm_Game_World.history_on_turn at hh
    rw [hh] at leg
    rw [hc] at leg
    · dsimp [snd_strat_conditioned]
      dsimp [fst_strat_conditioned] at leg
      rw [dif_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)] at leg
      rw [dif_pos (by rw [List.getLast_append] ; apply f_act_leg)] at leg
      rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)] at leg
      dsimp at leg
      rw [List.append_nil] at leg
      have := h_f_strat ((Symm_Game_World.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toSymm_Game_World
              (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
              (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t ++
              [fst_s g.init_game_state []])) [f_act]
              (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)
              (by apply List.cons_ne_nil)
              (by rw [List.getLast_append] ; apply f_act_leg)
              (by apply f_act_leg)
              (by rw [List.getLast_append] ; dsimp)
      unfold Symm_Game_World.history_on_turn at this
      rw [this] at leg
      rw [List.getLast_append] at leg
      apply leg
    · apply f_act_leg
  · intro leg t ts
    cases' t with t
    · contradiction
    · have hh := g.history_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg t
      have hc := careless_singleton _ _ _ _ _ (g.law_careless)
      specialize leg (t) (by rw [Turn_fst_snd_step] ; exact ts)
      unfold Symm_Game_World.history_on_turn at hh
      rw [hh]
      rw [hc]
      · rw [zSymm_Game_World.world_after_fst_law] at leg
        convert leg using 1
        dsimp [fst_strat_conditioned]
        rw [dif_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)]
        rw [dif_pos (by rw [List.getLast_append] ; apply f_act_leg)]
        rw [List.dropLast_append_of_ne_nil _ (show [f_act] ≠ [] from by apply List.cons_ne_nil)]
        dsimp
        rw [List.append_nil]
        have := h_f_strat ((Symm_Game_World.history_on_turn (world_after_fst g (fst_s g.init_game_state []) f_act_leg).toSymm_Game_World
                (f_strat [fst_s g.init_game_state []] ((by apply List.cons_ne_nil) : [fst_s g.init_game_state []] ≠ []) f_act_leg)
                (snd_strat_conditioned fst_s (fst_s g.init_game_state []) g) t ++
                [fst_s g.init_game_state []])) [f_act]
                (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)
                (by apply List.cons_ne_nil)
                (by rw [List.getLast_append] ; apply f_act_leg)
                (by apply f_act_leg)
                (by rw [List.getLast_append] ; dsimp)
        unfold Symm_Game_World.history_on_turn at this
        rw [this]
        rw [List.getLast_append]
        rfl
      · apply f_act_leg



lemma zSymm_Game_World.conditioned_state_on_turn_neutral
  [Inhabited β] (g : zSymm_Game_World α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.law g.init_game_state [] (h.getLast hne)) → (Hl : g.law g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.law g.init_game_state [] (fst_s g.init_game_state [])):
  let f_act := fst_s g.init_game_state []
  ∀ t : ℕ,
  g.state_on_turn_neutral fst_s (g.fst_strat_conditioned f_strat) (t+1) =
  (g.world_after_fst f_act f_act_leg).state_on_turn_neutral (f_strat [f_act] (List.cons_ne_nil f_act []) f_act_leg) (g.snd_strat_conditioned fst_s f_act) t:=
  by
  intro f_act t
  dsimp [Symm_Game_World.state_on_turn_neutral]
  rw [g.state_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg]
  by_cases q : Turn_fst t
  · rw [if_pos q]
    rw [Turn_fst_not_step] at q
    rw [if_neg q]
  · rw [if_neg q]
    rw [Turn_fst_not_step, not_not] at q
    rw [if_pos q]




lemma History_on_turn_eq_strats_snd
  (g : zSymm_Game_World α β) (f_strat sSa aSb: Strategy α β)
  (h : ∀ t, Turn_snd (t+1) →  sSa g.init_game_state (History_on_turn g.init_game_state f_strat sSa (t)) =
          sSb g.init_game_state (History_on_turn g.init_game_state f_strat sSb (t))) :
  History_on_turn g.init_game_state f_strat sSa = History_on_turn g.init_game_state f_strat sSb :=
  by
  funext t
  induction' t with t ih
  · dsimp [History_on_turn]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q, if_pos q, ih]
    · specialize h t (by rw [Turn_not_fst_iff_snd] at q ; exact q)
      rw [if_neg q, if_neg q, h, ih]


lemma Strategy_legal_fst_eq_strats_snd
  (g : zSymm_Game_World α β) (f_strat sSa sSb: Strategy α β)
  (h : ∀ t, Turn_snd (t+1) → sSa g.init_game_state (History_on_turn g.init_game_state f_strat sSa (t)) =
          sSb g.init_game_state (History_on_turn g.init_game_state f_strat sSb (t)))
  (hl : Strategy_legal_fst g.init_game_state g.law f_strat sSa) :
  Strategy_legal_fst g.init_game_state g.law f_strat sSb :=
  by
  intro t tf
  rw [← History_on_turn_eq_strats_snd g f_strat sSa sSb h]
  exact hl t tf


lemma Strategy_legal_snd_eq_strats_snd
  (g : zSymm_Game_World α β) (f_strat sSa sSb: Strategy α β)
  (h : ∀ t, Turn_snd (t+1) → sSa g.init_game_state (History_on_turn g.init_game_state f_strat sSa (t)) =
          sSb g.init_game_state (History_on_turn g.init_game_state f_strat sSb (t)))
  (hl : Strategy_legal_snd g.init_game_state g.law f_strat sSa) :
  Strategy_legal_snd g.init_game_state g.law f_strat sSb :=
  by
  intro t ts
  rw [← History_on_turn_eq_strats_snd g f_strat sSa sSb h]
  specialize hl t ts
  rw [h t ts, ← History_on_turn_eq_strats_snd g f_strat sSa sSb h] at hl
  exact hl



lemma Conditioning_win [Inhabited β] (g : zSymm_Game_World α β) (fst_s: Strategy α β)
  (f_strat : (h : List β) → (hne : h ≠ []) → (hl : g.law g.init_game_state [] (h.getLast hne)) → Strategy α β)
  (h_f_strat : ∀ h H: List β, (hne : h ≠ []) → (Hne : H ≠ []) →
      (hl : g.law g.init_game_state [] (h.getLast hne)) → (Hl : g.law g.init_game_state [] (H.getLast Hne)) →
      h.getLast hne = H.getLast Hne →
      f_strat h hne hl = f_strat H Hne Hl)
  (f_act_leg : g.law g.init_game_state [] (fst_s g.init_game_state []))
  (Leg_f : Strategy_legal_fst g.init_game_state g.law fst_s (zSymm_Game_World.fst_strat_conditioned g f_strat))
  (Leg_s : Strategy_legal_snd g.init_game_state g.law fst_s (zSymm_Game_World.fst_strat_conditioned g f_strat))
  (wlg_ws : ¬Symm_Game_World.win_states g.toSymm_Game_World g.init_game_state)
  (hw : let f_act := fst_s g.init_game_state []
        Symm_Game.fst_win { toSymm_Game_World := (g.world_after_fst f_act f_act_leg).toSymm_Game_World,
                              fst_strat := f_strat [f_act] (by apply List.cons_ne_nil) f_act_leg,
                              snd_strat := g.snd_strat_conditioned fst_s f_act,
                              fst_lawful :=
                                (by
                                have := g.conditioned_legal_snd fst_s f_strat h_f_strat f_act_leg
                                dsimp at this
                                rw [zSymm_Game_World.world_after_fst_law, ← this]
                                exact Leg_s),
                              snd_lawful :=
                                (by
                                have := g.conditioned_legal_fst fst_s f_strat h_f_strat f_act_leg
                                dsimp at this
                                rw [zSymm_Game_World.world_after_fst_law, ← this]
                                exact Leg_f),
                                }) :
    Symm_Game.snd_win { toSymm_Game_World := g.toSymm_Game_World,
                          fst_strat := fst_s,
                          snd_strat := (zSymm_Game_World.fst_strat_conditioned g f_strat),
                          fst_lawful := (Leg_f),
                          snd_lawful := (Leg_s)} :=
  by
  obtain ⟨t, ⟨ts,tw,tn⟩⟩ := hw
  use (t+1)
  constructor
  · rw [← Turn_fst_snd_step]
    exact ts
  · constructor
    · dsimp at tw
      convert tw using 1
      apply g.state_on_turn_conditioned fst_s f_strat h_f_strat f_act_leg
    · intro n nt
      cases' n with n
      · dsimp [Symm_Game.state_on_turn_neutral]
        rw [if_neg (by decide)]
        dsimp [Symm_Game.state_on_turn]
        exact wlg_ws
      · have := g.conditioned_state_on_turn_neutral fst_s f_strat h_f_strat f_act_leg n
        apply Symm_Game.state_on_turn_neutral_from_World _ (n+1)
        dsimp
        rw [this]
        apply tn
        exact Nat.lt_of_add_lt_add_right nt


-- # Even more conditioining

def zSymm_Game_World.snd_strat_reconditioned (s_strat : Strategy α β) (f_act : β) (g : zSymm_Game_World α β) (f_act_leg : g.law g.init_game_state [] f_act) : Strategy α β :=
  fun _ hist => if hist = [] then f_act else s_strat (g.world_after_fst f_act f_act_leg).init_game_state (hist.dropLast)

def zSymm_Game_World.fst_strat_reconditioned (f_strat : Strategy α β) (f_act : β) (g : zSymm_Game_World α β) : Strategy α β :=
  fun _ hist => f_strat g.init_game_state (hist ++ [f_act])


lemma zSymm_Game_World.history_reconditioned
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β) :
  ∀ t : ℕ,
  History_on_turn g.init_game_state (g.snd_strat_reconditioned ws f_act f_act_leg) snd_s (t+1) =
  History_on_turn (world_after_fst g f_act f_act_leg).init_game_state (g.fst_strat_reconditioned snd_s f_act) ws (t) ++ [f_act]
  :=
  by
  intro t
  induction' t with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by decide)]
    dsimp [snd_strat_reconditioned]
    rw [if_pos (by rfl)]
  · unfold History_on_turn
    by_cases q : Turn_fst (t+1+1)
    · rw [if_pos q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at q
      rw [if_neg q]
      dsimp [snd_strat_reconditioned, fst_strat_reconditioned]
      rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
      congr
      rw [ih]
      rw [List.dropLast_append_of_ne_nil]
      · dsimp
        rw [List.append_nil]
      · apply List.cons_ne_nil
    · rw [if_neg q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at q
      rw [if_pos q]
      dsimp [snd_strat_reconditioned, fst_strat_reconditioned]
      congr


lemma zSymm_Game_World.snd_reconditioned_legal
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β)
  (hf : Strategy_legal_fst g.init_game_state g.law (snd_strat_reconditioned ws f_act g f_act_leg) snd_s)
  : Strategy_legal_snd (world_after_fst g f_act f_act_leg).toSymm_Game_World.init_game_state
      (world_after_fst g f_act f_act_leg).toSymm_Game_World.law (fst_strat_reconditioned snd_s f_act g) ws
  :=
  by
  intro t ts
  specialize hf (t+1) (by rw [← Turn_snd_fst_step] ; exact ts)
  rw [g.history_reconditioned] at hf
  have := (g.hyper_legal_blind_toStrong g.is_hyper_legal_blind).2
  dsimp [Symm_Game_World.strong_legal_blind_snd] at this
  rw [← this] at hf
  clear this
  rw [zSymm_Game_World.world_after_fst_law]
  convert hf using 1
  · dsimp [snd_strat_reconditioned]
    rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil f_act [])]
    congr
    rw [List.dropLast_append_of_ne_nil]
    · dsimp
      rw [List.append_nil]
    · apply List.cons_ne_nil
  · apply f_act_leg

lemma zSymm_Game_World.snd_reconditioned_legal'
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β)
  (hf : Strategy_legal_snd (world_after_fst g f_act f_act_leg).toSymm_Game_World.init_game_state
      (world_after_fst g f_act f_act_leg).toSymm_Game_World.law (fst_strat_reconditioned snd_s f_act g) ws)
  : Strategy_legal_fst g.init_game_state g.law (snd_strat_reconditioned ws f_act g f_act_leg) snd_s
  :=
  by
  intro t tf
  cases' t with t
  · dsimp [History_on_turn, snd_strat_reconditioned]
    rw [if_pos (by rfl)]
    exact f_act_leg
  · specialize hf t (by rw [Turn_snd_fst_step] ; exact tf)
    rw [g.history_reconditioned]
    have := (g.hyper_legal_blind_toStrong g.is_hyper_legal_blind).2
    dsimp [Symm_Game_World.strong_legal_blind_snd] at this
    rw [← this]
    clear this
    rw [zSymm_Game_World.world_after_fst_law] at hf
    convert hf using 1
    · dsimp [snd_strat_reconditioned]
      rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil f_act [])]
      congr
      rw [List.dropLast_append_of_ne_nil]
      · dsimp
        rw [List.append_nil]
      · apply List.cons_ne_nil
    · apply f_act_leg



lemma zSymm_Game_World.fst_reconditioned_legal
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β)
  (hs : Strategy_legal_snd g.init_game_state g.law (snd_strat_reconditioned ws f_act g f_act_leg) snd_s)
  : Strategy_legal_fst (world_after_fst g f_act f_act_leg).toSymm_Game_World.init_game_state
      (world_after_fst g f_act f_act_leg).toSymm_Game_World.law (fst_strat_reconditioned snd_s f_act g) ws
  :=
  by
  intro t ts
  specialize hs (t+1) (by rw [← Turn_fst_snd_step] ; exact ts)
  rw [g.history_reconditioned] at hs
  have := (g.hyper_legal_blind_toStrong g.is_hyper_legal_blind).2
  dsimp [Symm_Game_World.strong_legal_blind_snd] at this
  rw [← this] at hs
  clear this
  rw [zSymm_Game_World.world_after_fst_law]
  convert hs using 1
  apply f_act_leg



lemma zSymm_Game_World.state_reconditioned
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β) :
  ∀ t : ℕ,
  g.state_on_turn (g.snd_strat_reconditioned ws f_act f_act_leg) snd_s (t+1) =
  (world_after_fst g f_act f_act_leg).state_on_turn (g.fst_strat_reconditioned snd_s f_act) ws (t)
  :=
  by
  intro t
  cases' t with t
  · dsimp [Symm_Game_World.state_on_turn, Game_World.history_on_turn, History_on_turn, snd_strat_reconditioned]
    rw [if_pos (by decide)]
    rw [if_pos (by rfl)]
    rfl
  · dsimp [Symm_Game_World.state_on_turn]
    by_cases q : Turn_fst (t + 1 + 1)
    · rw [if_pos q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at q
      rw [if_neg q]
      have := careless_singleton _ _ _ _ _ g.transition_careless
      unfold Symm_Game_World.history_on_turn
      rw [zSymm_Game_World.history_reconditioned]
      rw [this]
      · congr
        dsimp [snd_strat_reconditioned]
        rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; apply List.cons_ne_nil)]
        rw [List.dropLast_append_of_ne_nil]
        · dsimp
          rw [List.append_nil]
        · apply List.cons_ne_nil
      · apply f_act_leg
    · rw [if_neg q]
      rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at q
      rw [if_pos q]
      have := careless_singleton _ _ _ _ _ g.transition_careless
      unfold Symm_Game_World.history_on_turn
      rw [zSymm_Game_World.history_reconditioned]
      rw [this]
      · congr
      · apply f_act_leg



lemma zSymm_Game_World.state_neutral_reconditioned
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β) :
  ∀ t : ℕ,
  g.state_on_turn_neutral (g.snd_strat_reconditioned ws f_act f_act_leg) snd_s (t+1) =
  (world_after_fst g f_act f_act_leg).state_on_turn_neutral (g.fst_strat_reconditioned snd_s f_act) ws (t)
  :=
  by
  intro t
  unfold Symm_Game_World.state_on_turn_neutral
  by_cases q : Turn_fst (t + 1)
  · rw [if_pos q]
    rw [iff_not_comm.mp (Turn_fst_not_step (t))] at q
    rw [if_neg q]
    rw [zSymm_Game_World.world_after_fst_win_states]
    congr 2
    apply zSymm_Game_World.state_reconditioned
  · rw [if_neg q]
    rw [iff_not_comm.mp (Turn_fst_not_step (t)), not_not] at q
    rw [if_pos q]
    rw [zSymm_Game_World.world_after_fst_win_states]
    congr 2
    apply zSymm_Game_World.state_reconditioned





lemma zSymm_Game_World.reCondition_win
  (g : zSymm_Game_World α β) (f_act : β) (f_act_leg : g.law g.init_game_state [] f_act)
  (snd_s ws : Strategy α β)
  (ws_leg : Strategy_legal_fst g.init_game_state g.law (snd_strat_reconditioned ws f_act g f_act_leg) snd_s)
  (snd_leg : Strategy_legal_snd g.init_game_state g.law (snd_strat_reconditioned ws f_act g f_act_leg) snd_s)
  (wlg_ws : ¬Symm_Game_World.win_states g.toSymm_Game_World g.init_game_state)
  (H : Symm_Game.snd_win
    { toSymm_Game_World := (g.world_after_fst f_act f_act_leg).toSymm_Game_World,
      fst_strat := g.fst_strat_reconditioned snd_s f_act,
      snd_strat := ws,
      fst_lawful :=
          (by
           apply zSymm_Game_World.fst_reconditioned_legal
           exact snd_leg)
      snd_lawful :=
        (by
           apply zSymm_Game_World.snd_reconditioned_legal
           exact ws_leg)
      })
  : Symm_Game.fst_win
  { toSymm_Game_World := g.toSymm_Game_World, fst_strat := snd_strat_reconditioned ws f_act g f_act_leg, snd_strat := snd_s,
    fst_lawful := ws_leg, snd_lawful := snd_leg } :=
  by
  obtain ⟨t,ts,tw,tn⟩ := H
  use (t+1)
  constructor
  · rw [← Turn_snd_fst_step]
    exact ts
  · constructor
    · dsimp
      rw [zSymm_Game_World.world_after_fst_win_states] at tw
      convert tw using 1
      apply zSymm_Game_World.state_reconditioned
    · intro n nt
      cases' n with n
      · dsimp [Symm_Game.state_on_turn_neutral]
        rw [if_neg (by decide)]
        dsimp [Symm_Game.state_on_turn]
        exact wlg_ws
      · have := g.state_neutral_reconditioned
        apply Symm_Game.state_on_turn_neutral_from_World _ (n+1)
        dsimp
        rw [this]
        apply tn
        exact Nat.lt_of_add_lt_add_right nt
