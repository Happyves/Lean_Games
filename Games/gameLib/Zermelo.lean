/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Mathlib.Tactic



/-
Note to self:

Use conditionning as follows: we have the property of game that termintae
at turn 0 and we know that for all games and teruns t, if the property is
true for games that terminta before t, then it is also true for games that
terminate before t+1. Then by basic induction on t we know that it's true
for all game worlds that terminate before some t.

For zermelo, given a game world that terminates before t+1, look at all
those, indexed by the first move, hence indexed over β, where the first
move yields the initial state. Show that these game worlds must terminate
before t.
-/

inductive Game_World_wDraw.has_WLD (g : Game_World_wDraw α β) : Prop where
| wf : g.is_fst_win → g.has_WLD
| ws : g.is_snd_win → g.has_WLD
| d : g.is_draw → g.has_WLD



def Game_World_wDraw.world_after_fst {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : Game_World_wDraw α β := -- act not required to be legal
  {g with init_game_state := g.fst_transition [] fst_act }
  -- maybe swap fst and snd notions ? Cause we expect snd player to go fst now



@[simp]
lemma Game_World_wDraw.world_after_fst_init {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.fst_transition [] fst_act :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_fst_legal {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_legal = g.fst_legal :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_snd_legal {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_legal = g.snd_legal :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_fst_win_states {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_win_states = g.fst_win_states :=
  by rfl


@[simp]
lemma Game_World_wDraw.world_after_fst_snd_win_states {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_win_states = g.snd_win_states :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_draw_states {α β : Type u} (g : Game_World_wDraw α β)
  (fst_act : β) : (g.world_after_fst fst_act).draw_states = g.draw_states :=
  by rfl


/-
DIDN'T NEED THIS ?

In chess, imaging a board with pieces at random, and consider two situations.
In the first, the first player makes a move and then the second one does.
In the second situation, the board is that of the first situation, but we ask the
second player to move first. Will the second players moves be the same in both
situations ?
They don't have to. After all, in the first scenario, the second player gains
some knowledge about how the first plays...
We'll call strategies that play the same in both situations "careless".
-/

def Game_World_wDraw.Strategy_careless (strat : Strategy α β) (g : Game_World_wDraw α β): Prop :=
  ∀ f_act : β, ∀ hist : List β, strat (g.fst_transition [] f_act) hist = strat g.init_game_state (hist ++ [f_act])

/-
In ↑, we can't just have hist = [] and deduce the ↑ from this case : the moves
for these two scenarios may be the same at that stage, but they could begin
to differ at future stages

Example for PUB in `Careless_Example`
-/


/--
The action is legal on turn t in the game with initial state being the state after f's first move,
where s plays first and f second, iff it it legal on turn t+1 of the original game.
-/
def Game_World_wDraw.law_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β,
  ∀ turn : ℕ, ∀ act : β, g.snd_legal (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) act
    ↔ g.fst_legal (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) act

def Game_World_wDraw.law_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β,
  ∀ turn : ℕ, ∀ act : β, g.fst_legal (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) act
    ↔ g.snd_legal (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) act

def Game_World_wDraw.law_blind (g : Game_World_wDraw α β) : Prop :=
  g.law_blind_fst ∧ g.law_blind_snd


instance (l : List α): Decidable (l = []) :=
  by
  match l with
  | [] => apply isTrue ; rfl
  | x :: L => apply isFalse ; exact List.cons_ne_nil x L







def Game_World_wDraw.law_blind_fst' (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.snd_legal (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    ↔ g.fst_legal (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Game_World_wDraw.law_blind_snd' (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.fst_legal (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    ↔ g.snd_legal (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Game_World_wDraw.law_blind' (g : Game_World_wDraw α β) : Prop :=
 g.law_blind_fst' ∧ g.law_blind_snd'

-- TODO : Try to prove legality stuff with this notion of blindness, then maybe try to weaken it

lemma Game_World_wDraw.History_of_preconditioned'
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  History_on_turn g.init_game_state fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) ++ [fst_act] :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [History_on_turn, Turn_fst]
    rw [if_pos (by decide), if_pos (by rfl)]
  · dsimp only [History_on_turn] at *
    by_cases q : Turn_fst (t+1)
    · rw [Turn_fst_not_step] at q
      rw [if_neg q] at *
      rw [← Turn_fst_not_step] at q
      rw [if_pos q, if_pos q] at *
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Game_World_wDraw.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]
    · rw [if_neg q, if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q] at *
      rw [if_neg (by apply List.cons_ne_nil)]
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Game_World_wDraw.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]


def Game_World_wDraw.transition_blind_fst (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.snd_transition (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.fst_transition (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act

def Game_World_wDraw.transition_blind_snd (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat: Strategy α β, ∀ fst_act : β, g.fst_legal [] fst_act →
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  ∀ turn : ℕ, ∀ act : β, g.fst_transition (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) act
    = g.snd_transition (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) act


def Game_World_wDraw.transition_blind (g : Game_World_wDraw α β) : Prop :=
 g.transition_blind_fst ∧ g.transition_blind_snd



lemma Game_World_wDraw.State_of_preconditioned
  (g: Game_World_wDraw α β)
  (tb : g.transition_blind)
  (fst_act: β)
  (fst_act_legal: g.fst_legal [] fst_act)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  g.state_on_turn fst_strat snd_strat (turn + 1) =
  (g.world_after_fst fst_act).state_on_turn f_strat s_strat turn :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [state_on_turn]
    rw [if_pos (by decide)]
    dsimp [history_on_turn, History_on_turn]
    rw [if_pos (by rfl)]
  · dsimp [state_on_turn]
    by_cases q : Turn_fst (t + 1)
    · rw [if_pos q]
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      dsimp [history_on_turn]
      have := g.History_of_preconditioned' fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.2 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (f_strat (world_after_fst g fst_act).toGame_World.init_game_state (History_on_turn (world_after_fst g fst_act).toGame_World.init_game_state f_strat s_strat t))
      rw [Game_World_wDraw.world_after_fst_init] at this
      rw [← this]
      clear this
      rfl
    · rw [Turn_not_fst_iff_snd, Turn_snd_fst_step] at q
      rw [if_pos q]
      dsimp [history_on_turn]
      rw [← Turn_fst_step, Turn_fst_not_step] at q
      rw [if_neg q]
      rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
      have := g.History_of_preconditioned' fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← this]
      clear this
      have := tb.1 f_strat s_strat fst_act fst_act_legal
      dsimp at this
      specialize this t (s_strat (Game_World.fst_transition g.toGame_World [] fst_act) (History_on_turn (Game_World.fst_transition g.toGame_World [] fst_act) f_strat s_strat t))
      rw [← this]
      clear this
      rfl


lemma Game_World_wDraw.fst_legal_preconditioned'
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal [] fst_act)
  (f_strat s_strat : Strategy α β)
  (s_leg: Strategy_legal_snd (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).snd_legal) f_strat s_strat)
  (b : g.law_blind_fst')
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal_fst g.init_game_state (fun x => g.fst_legal) fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · dsimp [History_on_turn]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · rw [← b, Game_World_wDraw.History_of_preconditioned']
    · dsimp [History_on_turn]
      rw [if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil fst_act [])]
      rw [List.dropLast_concat]
      apply s_leg
      rw [Turn_snd_fst_step]
      exact tf
    · exact fst_act_legal


lemma Game_World_wDraw.snd_legal_preconditioned'
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal [] fst_act)
  (f_strat s_strat : Strategy α β)
  (f_leg: Strategy_legal_fst (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).fst_legal) f_strat s_strat)
  (b : g.law_blind_snd')
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal_snd g.init_game_state (fun x => g.snd_legal) fst_strat snd_strat :=
  by
  intro fst_strat snd_strat t tf
  cases' t with t
  · contradiction
  · rw [← b, Game_World_wDraw.History_of_preconditioned']
    · dsimp [History_on_turn]
      rw [List.dropLast_concat]
      apply f_leg
      rw [Turn_fst_snd_step]
      exact tf
    · exact fst_act_legal

--#exit

inductive Game_World_wDraw.State_is_ws_d (g : Game_World_wDraw α β) (s : α) : Prop where
| ws : g.snd_win_states s → g.State_is_ws_d s
| d : g.draw_states s → g.State_is_ws_d s

lemma Game_World_wDraw.init_wld_of_turn_zero_wld
  (g : Game_World_wDraw α β)
  (f_strat s_strat : Strategy α β):
  g.Turn_isWLD f_strat s_strat 0 → g.State_is_ws_d g.init_game_state :=
  by
  intro t0
  cases' t0 with wf ws d
  · contradiction
  · rename_i h
    dsimp [state_on_turn] at h
    apply Game_World_wDraw.State_is_ws_d.ws
    exact h
  · rename_i h
    dsimp [state_on_turn] at h
    apply Game_World_wDraw.State_is_ws_d.d
    exact h

def Game_World_wDraw.nontrivial (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat : Strategy α β, ¬ (g.Turn_isWLD f_strat s_strat 0)

structure Game_World_wDraw.coherent_end_aux
  (g : Game_World_wDraw α β) (f_strat s_strat : Strategy α β) (t : ℕ) : Prop where
  f : g.fst_win_states (g.state_on_turn f_strat s_strat t) → g.fst_win_states (g.state_on_turn f_strat s_strat (t+1))
  s : g.snd_win_states (g.state_on_turn f_strat s_strat t) → g.snd_win_states (g.state_on_turn f_strat s_strat (t+1))
  d : g.draw_states (g.state_on_turn f_strat s_strat t) → g.draw_states (g.state_on_turn f_strat s_strat (t+1))

def Game_World_wDraw.coherent_end (g : Game_World_wDraw α β) : Prop :=
  ∀ f_strat s_strat : Strategy α β, ∀ t : ℕ, g.coherent_end_aux f_strat s_strat t



def Game_World_wDraw.win_state_eq (g : Game_World_wDraw α β) : Prop :=
  ∀ a : α, g.fst_win_states a ↔ g.snd_win_states a


lemma Game_World_wDraw.conditioning_bound
  (g : Game_World_wDraw α β)
  {T : ℕ} (hg : g.isWLD_wBound (T + 1))
  (fst_act : β) (leg : g.fst_legal [] fst_act)
  (b : g.law_blind') (nt : g.coherent_end) (tb : g.transition_blind) (wb : g.win_state_eq):
  (g.world_after_fst fst_act).isWLD_wBound T :=
  by
  intro f_strat s_strat f_leg s_leg
  let fst_strat : Strategy α β := fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)
  let snd_strat : Strategy α β := fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)
  specialize hg fst_strat snd_strat _ _
  · apply g.fst_legal_preconditioned' fst_act leg  f_strat s_strat s_leg b.1
  · apply g.snd_legal_preconditioned' fst_act leg  f_strat s_strat f_leg b.2
  · obtain ⟨t, t_bd, t_prop⟩ := hg
    cases' t with t
    · use 0
      constructor
      · exact Nat.zero_le T
      · cases' t_prop
        · rename_i no pe ; contradiction
        · rename_i c
          apply Turn_isWLD.ws
          · decide
          · dsimp [state_on_turn]
            have := (nt fst_strat snd_strat 0).s c
            dsimp [state_on_turn] at this
            rw [if_pos (by decide)] at this
            dsimp [history_on_turn, History_on_turn] at this
            rw [if_pos (by rfl)] at this
            exact this
        · rename_i c
          apply Turn_isWLD.d
          dsimp [state_on_turn]
          have := (nt fst_strat snd_strat 0).d c
          dsimp [state_on_turn] at this
          rw [if_pos (by decide)] at this
          dsimp [history_on_turn, History_on_turn] at this
          rw [if_pos (by rfl)] at this
          exact this
    · rw [Nat.succ_le_succ_iff] at t_bd
      use t
      constructor
      · exact t_bd
      · cases' t_prop with tp c tp c c
        · apply Turn_isWLD.ws
          · rw [Turn_snd_fst_step] ; exact tp
          · rw [← Game_World_wDraw.State_of_preconditioned]
            · rw [Game_World_wDraw.world_after_fst_snd_win_states]
              rw [wb] at c
              exact c
            · exact tb
            · exact leg
        · apply Turn_isWLD.wf
          · rw [Turn_fst_snd_step] ; exact tp
          · rw [← Game_World_wDraw.State_of_preconditioned]
            · rw [Game_World_wDraw.world_after_fst_fst_win_states]
              rw [← wb] at c
              exact c
            · exact tb
            · exact leg
        · apply Turn_isWLD.d
          · rw [← Game_World_wDraw.State_of_preconditioned]
            · rw [Game_World_wDraw.world_after_fst_draw_states]
              exact c
            · exact tb
            · exact leg




def Game_World_wDraw.playable (g : Game_World_wDraw α β) : Prop :=
  ∃ f_strat s_strat : Strategy α β,
  (Strategy_legal_fst g.init_game_state (fun _ => g.fst_legal) f_strat s_strat) ∧
  (Strategy_legal_snd g.init_game_state (fun _ => g.snd_legal) f_strat s_strat)


structure Game_World_wDraw.assumptions (g : Game_World_wDraw α β) : Prop where
 pl : g.playable
 bl : g.law_blind'
 nt : g.coherent_end
 tb : g.transition_blind
 wb : g.win_state_eq

lemma Game_World_wDraw.win_state_eq_world_after_fst
  (g : Game_World_wDraw α β) (fst_act: β) :
  g.win_state_eq ↔ (g.world_after_fst fst_act).win_state_eq :=
  by
  dsimp [Game_World_wDraw.win_state_eq]
  rfl


lemma Game_World_wDraw.History_of_reconditioned
  (g: Game_World_wDraw α β)
  (fst_act: β)
  (fst_strat snd_strat : Strategy α β)
  (hfa : fst_act = fst_strat g.init_game_state [])
  (turn : ℕ):
  let f_strat : Strategy α β := fun _ hist => snd_strat g.init_game_state (hist ++ [fst_act])
  let s_strat : Strategy α β := fun _ hist => fst_strat g.init_game_state (hist ++ [fst_act])
  History_on_turn g.init_game_state fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) ++ [fst_act] :=
  by
  intro f_strat s_strat
  induction' turn with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by decide)]
    rw [hfa]
  · sorry



--#exit

lemma Game_World_wDraw.assumptions_invar (g : Game_World_wDraw α β)
  (fst_act : β) (leg : g.fst_legal [] fst_act) :
  g.assumptions → (g.world_after_fst fst_act).assumptions :=
  by
  intro hg
  constructor
  · obtain ⟨fst_strat, snd_strat, fst_leg, snd_leg⟩ := hg.pl
    let f_strat : Strategy α β := fun _ hist => snd_strat g.init_game_state (hist ++ [fst_act])
    let s_strat : Strategy α β := fun _ hist => fst_strat g.init_game_state (hist ++ [fst_act])
    use f_strat
    use s_strat
    constructor
    · rw [Game_World_wDraw.world_after_fst_init, Game_World_wDraw.world_after_fst_fst_legal]
      intro t tf
      sorry
      -- cases' t with t
      -- · dsimp [History_on_turn]
    sorry


--#exit

lemma Game_World_wDraw.conditioning_WLD_helper
  (g : Game_World_wDraw α β)
  (hwld : g.has_WLD)
  (hnfw : ¬ g.is_snd_win)
  (hnd : ¬ g.is_draw) :
  g.is_fst_win :=
  by
  cases' hwld
  · assumption
  · contradiction
  · contradiction


open Classical

lemma History_zig_zag
  [Inhabited β]
  (g : Game_World_wDraw α β)
  (f_strat_wb f_strat_wa : Strategy α β)
  (h : ∀ fst_act : β, g.fst_legal [] fst_act → (g.world_after_fst fst_act).assumptions → (g.world_after_fst fst_act).has_WLD)
  (qws: ∀ (f_act : β), Game_World.fst_legal g.toGame_World [] f_act → (g.world_after_fst f_act).assumptions → ¬ (g.world_after_fst f_act).is_snd_win)
  (qd: ∀ (f_act : β), Game_World.fst_legal g.toGame_World [] f_act → (g.world_after_fst f_act).assumptions → ¬ (g.world_after_fst f_act).is_draw)
  :
  let s_strat_wa := fun ini hist => f_strat_wb g.init_game_state (hist ++  [f_strat_wb g.init_game_state []])
  let s_strat_wb := fun (ini : α) hist  =>
                                if hh : hist = [] -- shouldn't happen, as snd strat
                                then default -- dummy
                                else let f_act := List.getLast hist hh
                                     if H : g.fst_legal [] f_act ∧ (g.world_after_fst f_act).assumptions -- should be the cases ?!?
                                     then (Classical.choose ((g.world_after_fst f_act).conditioning_WLD_helper
                                                              (h f_act H.1 H.2)
                                                              (qws f_act H.1 H.2)
                                                              (qd f_act H.1 H.2)))
                                           ini hist.dropLast -- is it ? since ref to history in current game
                                     else default
  ∀ turn : ℕ,
  (History_on_turn (g.world_after_fst (f_strat_wb g.init_game_state [])).init_game_state f_strat_wa s_strat_wa turn) ++ [f_strat_wb g.init_game_state []]
  = History_on_turn g.init_game_state f_strat_wb s_strat_wb (turn +1) :=
  by
  sorry

-- State on turn next


--#exit


lemma Game_World_wDraw.conditioning_WLD
  [Inhabited β]
  (g : Game_World_wDraw α β)
  (h : ∀ fst_act : β, g.fst_legal [] fst_act → (g.world_after_fst fst_act).assumptions → (g.world_after_fst fst_act).has_WLD)
  :
  g.has_WLD :=
  by
  by_cases qws : ∃ f_act : β, g.fst_legal [] f_act ∧ (g.world_after_fst f_act).assumptions ∧ (g.world_after_fst f_act).is_snd_win
  · sorry -- remeber, fst becomes snd after fst move
  · push_neg at qws
    by_cases qd : ∃ f_act : β, g.fst_legal [] f_act ∧ (g.world_after_fst f_act).assumptions ∧ (g.world_after_fst f_act).is_draw
    · sorry
    · push_neg at qd
      apply Game_World_wDraw.has_WLD.ws
      let ws : Strategy α β := fun (ini : α) hist  =>
                                if hh : hist = [] -- shouldn't happen, as snd strat
                                then default -- dummy
                                else let f_act := List.getLast hist hh
                                     if H : g.fst_legal [] f_act ∧ (g.world_after_fst f_act).assumptions -- should be the cases ?!?
                                     then (Classical.choose ((g.world_after_fst f_act).conditioning_WLD_helper
                                                              (h f_act H.1 H.2)
                                                              (qws f_act H.1 H.2)
                                                              (qd f_act H.1 H.2)))
                                           ini hist.dropLast -- is it ? since ref to history in current game
                                     else default
      use ws
      intro f_strat ws_leg f_leg
      let f_act := f_strat g.init_game_state []
      set WS := ws g.init_game_state (History_on_turn g.init_game_state f_strat ws (0+1)) with WS_def
      have uno : ∀ t : ℕ, (History_on_turn g.init_game_state f_strat ws (t+1)) ≠ [] := by apply History_on_turn_nonempty_of_succ
      have dos : ∀ t : ℕ, (History_on_turn g.init_game_state f_strat ws (t+1)).getLast (uno t) = f_act :=
        by
        dsimp [f_act]
        apply History_on_turn_getLast_fst_act
      have tres : ∀ t : ℕ, g.fst_legal [] ((History_on_turn g.init_game_state f_strat ws (t+1)).getLast (uno t)) :=
        by
        intro t
        rw [dos t]
        dsimp [f_act]
        specialize f_leg 0 (by decide)
        dsimp [History_on_turn] at f_leg
        exact f_leg
      have quatro : (g.world_after_fst f_act).assumptions :=
        by
        dsimp [f_act]
        sorry
        -- use : Game_World_wDraw.win_state_eq_world_after_fst

      -- apriori useless
      -- have unpack : WS = choose (_ : is_snd_win (world_after_fst g f_act)) g.init_game_state (History_on_turn g.init_game_state f_strat ws (0 + 1))
      --     :=
      --     by
      --     dsimp [ws]
      --     rw [dif_neg (by apply uno)]
      --     rw [dif_pos ⟨(by apply tres), (by apply quatro)⟩]
      have da_prop := choose_spec ((g.world_after_fst f_act).conditioning_WLD_helper
                                      (h f_act (by rw [← (dos 0)] ; apply tres) (quatro))
                                      (qws f_act (by rw [← (dos 0)] ; apply tres) quatro)
                                      (qd f_act (by rw [← (dos 0)] ; apply tres) quatro))
      specialize da_prop (fun _ hist => f_strat g.init_game_state (hist ++ [f_act]))
      specialize da_prop (by sorry) (by sorry)

      clear WS WS_def



      obtain ⟨t_w , t_f, t_wf, t_bn⟩ := da_prop
      use (t_w + 1)
      constructor
      · rw [← Turn_fst_snd_step] ; exact t_f
      · constructor
        · have := (g.win_state_eq_world_after_fst f_act).mpr quatro.wb
          rw [← this]
          -- use t_wf
          sorry
        · sorry

#check Game.state_on_turn_neutral

-- work on Game_World_wDraw.History_of_reconditioned and legality in its context next

#exit

lemma Game_World_wDraw.Zermelo
  [Inhabited β]
  (g : Game_World_wDraw α β)
  {T : ℕ} (hg : g.isWLD_wBound T)
  (hp : g.assumptions)
  : g.has_WLD :=
  by
  revert g
  induction' T with t ih
  · intro g t0 hp
    dsimp [isWLD_wBound] at t0
    obtain ⟨f_strat, s_strat, f_leg, s_leg⟩ := hp.pl
    obtain ⟨t, tl0, t_end⟩ := t0 f_strat s_strat f_leg s_leg
    rw [Nat.le_zero] at tl0
    rw [tl0] at t_end
    replace t_end := g.init_wld_of_turn_zero_wld f_strat s_strat t_end
    cases' t_end
    · apply Game_World_wDraw.has_WLD.ws
      use (fun _ _ => default)
      intro f_strat' leg f_leg'
      use 0
      constructor
      · decide
      · constructor
        · dsimp [Game.state_on_turn]
          rename_i h ; exact h
        · intro t ahhh ; contradiction
    · apply Game_World_wDraw.has_WLD.d
      right
      use (fun _ _ => default)
      intro f_strat' leg f_leg'
      use 0
      constructor
      · decide
      · constructor
        · dsimp [Game.state_on_turn]
          rename_i h ; exact h
        · intro t ahhh ; contradiction
  · intro g bd hp
    apply Game_World_wDraw.conditioning_WLD
    intro f_act f_leg pl
    apply ih
    · exact Game_World_wDraw.conditioning_bound g bd f_act f_leg hp.bl hp.nt hp.tb hp.wb
    · exact pl


theorem Game_World_Finite.Zermelo [Inhabited β] (g : Game_World_Finite α β) (hp : g.assumptions) :
  g.has_WLD :=
  by
  exact @Game_World_wDraw.Zermelo β α _ g.toGame_World_wDraw g.bound g.termination hp



#exit


-- # Initial stuff

inductive Game.is_win_loose_draw {α β : Type u} (g : Game α β) : Prop
| win_f : g.fst_win → g.is_win_loose_draw
| win_s : g.snd_win → g.is_win_loose_draw
| draw : g.draw → g.is_win_loose_draw


lemma Game.terminates_is_win_loose_draw {α β : Type u} (g : Game α β)
  (hg : g.terminates) : g.is_win_loose_draw :=
  by
  rw [Game.terminates] at hg
  obtain ⟨end_turn, end_turn_prop⟩ := hg
  by_cases q : (∀ t ≤ end_turn, g.state_on_turn_neutral t)
  · apply Game.is_win_loose_draw.draw
    use end_turn
  · push_neg at q
    have wf : _ := Nat.lt_wfRel.wf
    rw [WellFounded.wellFounded_iff_has_min] at wf
    specialize wf (fun t => t ≤ end_turn → ¬state_on_turn_neutral g t)
    dsimp [Set.Nonempty, Membership.mem, Set.Mem] at wf
    obtain ⟨it, it_bound, it_prop⟩ := q
    specialize wf ⟨it, (show _ from by intro ; exact it_prop)⟩
    obtain ⟨nnt, nnt_prop, nnt_min⟩ := wf
    have fact : nnt ≤ end_turn :=
      by
      apply le_trans _ it_bound
      specialize nnt_min it (show _ from by intro ; exact it_prop)
      rw [WellFoundedRelation.rel] at nnt_min
      rw [Game.state_on_turn_neutral] at nnt_prop
      -- I don't know why there's trouble here
      by_contra con
      rw [not_le] at con
      exact nnt_min con
    specialize nnt_prop fact
    rw [Game.state_on_turn_neutral] at nnt_prop
    split_ifs at nnt_prop with tc
    · rw [not_not] at nnt_prop
      apply Game.is_win_loose_draw.win_f
      use nnt
      constructor
      · exact tc
      · constructor
        · exact nnt_prop
        · intro t t_lt
          by_contra k
          specialize nnt_min t (show _ from by intro ; exact k)
          exact nnt_min t_lt
    · rw [not_not] at nnt_prop
      apply Game.is_win_loose_draw.win_s
      use nnt
      constructor
      · exact tc
      · constructor
        · exact nnt_prop
        · intro t t_lt
          by_contra k
          specialize nnt_min t (show _ from by intro ; exact k)
          exact nnt_min t_lt

inductive Symm_Game.is_win_loose_draw {α β : Type u} (g : Symm_Game α β) : Prop
| win_f : g.fst_win → g.is_win_loose_draw
| win_s : g.snd_win → g.is_win_loose_draw
| draw : g.draw → g.is_win_loose_draw

@[simp]
lemma Symm_Game.is_win_loose_draw_toGame {α β : Type u} (g : Symm_Game α β) :
  g.toGame.is_win_loose_draw ↔ g.is_win_loose_draw :=
  by
  constructor
  · intro G
    cases G with
    | win_f f => apply Symm_Game.is_win_loose_draw.win_f ; exact f
    | win_s s => apply Symm_Game.is_win_loose_draw.win_s ; exact s
    | draw f => apply Symm_Game.is_win_loose_draw.draw ; exact f
  · intro G
    cases G with
    | win_f f => apply Game.is_win_loose_draw.win_f ; exact f
    | win_s s => apply Game.is_win_loose_draw.win_s ; exact s
    | draw f => apply Game.is_win_loose_draw.draw ; exact f


lemma Symm_Game.terminates_is_win_loose_draw {α β : Type u} (g : Symm_Game α β)
  (hg : g.terminates) : g.is_win_loose_draw :=
  by
  rw [← Symm_Game.terminates_toGame] at hg
  rw [← Symm_Game.is_win_loose_draw_toGame]
  exact Game.terminates_is_win_loose_draw (toGame g) hg


inductive Game_World.has_win_loose_draw_strat {α β : Type u} (g : Game_World α β) : Prop
| win_f : g.is_fst_win → g.has_win_loose_draw_strat
| win_s : g.is_snd_win → g.has_win_loose_draw_strat
| draw : g.is_draw → g.has_win_loose_draw_strat


def Game_World.playable_fst {α β : Type u} (g : Game_World α β) : Prop :=
  (∃ e : Strategy α β, ∀ s : Strategy α β, Strategy_legal g.init_game_state (fun _ => g.fst_legal) e s e)

def Game_World.playable_snd {α β : Type u} (g : Game_World α β) : Prop :=
  (∃ e : Strategy α β, ∀ s : Strategy α β, Strategy_legal g.init_game_state (fun _ => g.snd_legal) s e e)

def Game_World.playable {α β : Type u} (g : Game_World α β) : Prop :=
  g.playable_fst ∧ g.playable_snd

-- non-playable worlds are for example those with law `fun _ _ _ => False`


def Game_World.playable' {α β : Type u} (g : Game_World α β) : Prop :=
  ∃ f : Strategy α β, ∃ s : Strategy α β,
    (Strategy_legal g.init_game_state (fun _ => g.fst_legal) f s f)
    ∧ (Strategy_legal g.init_game_state (fun _ => g.snd_legal) f s s)



def Game_World.world_after_fst {α β : Type u} (g : Game_World α β)
  (fst_act : β) : Game_World α β := -- act not required to be legal
  {g with init_game_state := g.fst_transition [] fst_act }
  -- maybe swap fst and snd notions ? Cause we expect snd player to go fst now

@[simp]
lemma Game_World.world_after_fst_init {α β : Type u} (g : Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.fst_transition [] fst_act :=
  by rfl

@[simp]
lemma Game_World.world_after_fst_fst_trans {α β : Type u} (g : Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_transition = g.fst_transition :=
  by rfl

@[simp]
lemma Game_World.world_after_fst_snd_trans {α β : Type u} (g : Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_transition = g.snd_transition :=
  by rfl

@[simp]
lemma Game_World.world_after_fst_fst_legal {α β : Type u} (g : Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).fst_legal = g.fst_legal :=
  by rfl

@[simp]
lemma Game_World.world_after_fst_snd_legal {α β : Type u} (g : Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).snd_legal = g.snd_legal :=
  by rfl


/-
In chess, imaging a board with pieces at random, and consider two situations.
In the first, the first player makes a move and then the second one does.
In the second situation, the board is that of the first situation, but we ask the
second player to move first. Will the second players moves be the same in both
situations ?
They don't have to. After all, in the first scenario, the second player gains
some knowledge about how the first plays...
We'll call strategies that play the same in both situations "careless".
-/

def Game_World.Strategy_careless (strat : Strategy α β) (g : Game_World α β): Prop :=
  ∀ f_act : β, ∀ hist : List β, strat (g.fst_transition [] f_act) hist = strat g.init_game_state (hist ++ [f_act])

/-
In ↑, we can't just have hist = [] and deduce the ↑ from this case : the moves
for these two scenarios may be the same at that stage, but they could begin
to differ at future stages

Example for PUB in `Careless_Example`
-/

def Symm_Game_World.Strategy_careless (strat : Strategy α β) (g : Symm_Game_World α β): Prop :=
  ∀ f_act : β, ∀ hist : List β, strat (g.transition [] f_act) hist = strat g.init_game_state (hist ++ [f_act])



lemma Game_World.world_after_fst_History (g : Game_World α β)
  (f_strat s_strat : Strategy α β) (turn : ℕ)
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat) :
  (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn)
  ++ [(f_strat g.init_game_state [])] = History_on_turn g.init_game_state f_strat s_strat (turn+1) :=
  by
  rw [History_on_turn]
  induction' turn with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by decide)]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t+1)
    · rw [if_pos q] at *
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      rw [← Turn_fst_not_step] at q
      rw [if_pos q]
      rw [Game_World.world_after_fst_init] at *
      rw [List.cons_append, ih]
      congr 1
      rw [hs, ih]
    · rw [if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q]
      rw [← @not_not (Turn_fst (t + 1 + 1)), ← Turn_fst_not_step] at q
      rw [if_neg q]
      rw [Game_World.world_after_fst_init] at *
      rw [List.cons_append, ih]
      congr 1
      rw [hf, ih]



lemma Game_World.Strategy_careless_act_on_turn_snd (g : Game_World α β) (f_strat s_strat: Strategy α β)
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat) (turn : ℕ) :
  s_strat (g.world_after_fst (f_strat g.init_game_state [])).init_game_state
    (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) =
  s_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) :=
  by
  rw [Game_World.world_after_fst_init, hs]
  congr
  apply Game_World.world_after_fst_History g f_strat s_strat turn hs hf



lemma Game_World.Strategy_careless_act_on_turn_fst (g : Game_World α β) (f_strat s_strat: Strategy α β)
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat) (turn : ℕ) :
  f_strat (g.world_after_fst (f_strat g.init_game_state [])).init_game_state
    (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) =
  f_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) :=
  by
  rw [Game_World.world_after_fst_init, hf]
  congr
  apply Game_World.world_after_fst_History g f_strat s_strat turn hs hf

/--
The action is legal on turn t in the game with initial state being the state after f's first move,
where s plays first and f second, iff it it legal on turn t+1 of the original game.
-/
def Game_World.law_blind_fst (g : Game_World α β) (f_strat s_strat: Strategy α β) : Prop :=
  ∀ turn : ℕ, ∀ act : β, g.snd_legal (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) act
    ↔ g.fst_legal (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) act

def Game_World.law_blind_snd (g : Game_World α β) (f_strat s_strat: Strategy α β) : Prop :=
  ∀ turn : ℕ, ∀ act : β, g.fst_legal (History_on_turn (g.world_after_fst (f_strat g.init_game_state [])).init_game_state s_strat f_strat turn) act
    ↔ g.snd_legal (History_on_turn g.init_game_state f_strat s_strat (turn + 1)) act

def Game_World.law_blind (g : Game_World α β) (f_strat s_strat: Strategy α β) : Prop :=
  g.law_blind_fst f_strat s_strat ∧ g.law_blind_snd f_strat s_strat


lemma Game_World.world_after_fst_legal (g : Game_World α β)
   (f_strat s_strat: Strategy α β) (h : Strategy_legal g.init_game_state (fun x => g.fst_legal) f_strat s_strat f_strat)
   (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
   (hg : g.law_blind f_strat s_strat):
   Strategy_legal (g.world_after_fst (f_strat g.init_game_state [])).init_game_state (fun x => (g.world_after_fst (f_strat g.init_game_state [])).snd_legal) s_strat f_strat f_strat :=
   by
   dsimp [Strategy_legal] at *
   intro t
   have := g.Strategy_careless_act_on_turn_fst f_strat s_strat hs hf t
   rw [Game_World.world_after_fst_init] at this
   rw [this]
   clear this
   obtain ⟨bf, bs⟩ := hg
   specialize h (t+1)
   specialize bf t (f_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (t + 1)))
   rw [← Game_World.world_after_fst_init, bf]
   exact h


lemma Game_World.world_after_snd_legal (g : Game_World α β)
   (f_strat s_strat: Strategy α β) (h : Strategy_legal g.init_game_state (fun x => g.snd_legal) f_strat s_strat s_strat)
   (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
   (hg : g.law_blind f_strat s_strat):
   Strategy_legal (g.world_after_fst (f_strat g.init_game_state [])).init_game_state (fun x => (g.world_after_fst (f_strat g.init_game_state [])).fst_legal) s_strat f_strat s_strat :=
   by
   dsimp [Strategy_legal] at *
   intro t
   have := g.Strategy_careless_act_on_turn_snd f_strat s_strat hs hf t
   rw [Game_World.world_after_fst_init] at this
   rw [this]
   clear this
   obtain ⟨bf, bs⟩ := hg
   specialize h (t+1)
   specialize bs t (s_strat g.init_game_state (History_on_turn g.init_game_state f_strat s_strat (t + 1)))
   rw [← Game_World.world_after_fst_init, bs]
   exact h


lemma Game_World.world_after_fst_legal' (g : Game_World α β)
  (f_strat s_strat: Strategy α β)
  (h : Strategy_legal (g.world_after_fst (f_strat g.init_game_state [])).init_game_state (fun x => g.snd_legal) s_strat f_strat f_strat)
  (hi : fst_legal g [] (f_strat g.init_game_state []))
  -- ↑ may not necessarily be ommitted. `f_strat g.init_game_state []` may not be legal, although
  -- `f_strat` is legal if we take the latters transition as initial turn ...
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
  (hg : g.law_blind f_strat s_strat) :
  Strategy_legal g.init_game_state (fun x => g.fst_legal) f_strat s_strat f_strat :=
  by
  dsimp [Strategy_legal] at *
  intro t
  cases' t with t
  · dsimp [History_on_turn]
    exact hi
  · rw [← (hg.1 t), Game_World.world_after_fst_init]
    rw [← Game_World.world_after_fst_History _ _ _ _ hs hf]
    specialize h t
    rw [← hf]
    apply h


lemma Game_World.world_after_snd_legal' (g : Game_World α β)
  (f_strat s_strat: Strategy α β)
  (h : Strategy_legal (g.world_after_fst (f_strat g.init_game_state [])).init_game_state (fun x => g.fst_legal) s_strat f_strat s_strat)
  (hi : snd_legal g [] (s_strat g.init_game_state []))
  -- ↑ never takes efect in practice, as second player doesn't have first turn,
  -- so this case has to be handled in the non-partial defintiion of the second strat...
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
  (hg : g.law_blind f_strat s_strat) :
  Strategy_legal g.init_game_state (fun x => g.snd_legal) f_strat s_strat s_strat :=
  by
  dsimp [Strategy_legal] at *
  intro t
  cases' t with t
  · dsimp [History_on_turn]
    exact hi
  · rw [← (hg.2 t), Game_World.world_after_fst_init]
    rw [← Game_World.world_after_fst_History _ _ _ _ hs hf]
    specialize h t
    rw [← hs]
    apply h


-- needed for `Game_World.world_after_fst_init_must_terminate`
instance (l : List α): Decidable (l = []) :=
  by
  match l with
  | [] => apply isTrue ; rfl
  | x :: L => apply isFalse ; exact List.cons_ne_nil x L


-- lemma name_1 (g : Game_World α β)
--   (fst_act: β)
--   (fst_act_legal: g.fst_legal [] fst_act)
--   (s_strat : Strategy α β) (turn : ℕ)
--   (hs : g.Strategy_careless s_strat) :
--   let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
--   fst_strat g.init_game_state (History_on_turn g.init_game_state fst_strat s_strat (turn+1)) =
--   s_strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst (fst_act)).init_game_state s_strat fst_strat turn) :=
--   by
--   intro fst_strat
--   dsimp
--   rw [if_neg _]
--   swap
--   · dsimp [History_on_turn]
--     split_ifs <;> decide
--   · rw [← Game_World.world_after_fst_History]
--     · rw [if_pos (by rfl)]
--       rw [List.dropLast_concat]
--       rfl
--     · exact hs
--     · intro a h
--       cases' h with x l
--       · dsimp
--         specialize hs fst_act []
--         dsimp at hs
--         sorry -- add as hypo ?

-- lemma name_2 (g : Game_World α β)
--   (fst_act: β)
--   (fst_act_legal: g.fst_legal [] fst_act)
--   (s_strat : Strategy α β)
--   (hs : g.Strategy_careless s_strat) :
--   let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
--   g.Strategy_careless fst_strat :=
--   by
--   intro fst_strat f_act hist
--   cases' hist with head tail
--   · dsimp
--     rw [if_pos (by rfl)]
--     rw [if_neg (by exact List.cons_ne_nil f_act [])]
--     sorry
--   · dsimp
--     rw [if_neg (by exact List.cons_ne_nil head tail)]
--     rw [if_neg (by exact List.cons_ne_nil head (tail ++ [f_act]))]


--#exit


-- lemma bgrbgwrj
--   (g: Game_World α β)
--   (fst_act: β)
--   (fst_act_legal: g.fst_legal [] fst_act)
--   --(hmm : g.law_blind_fst)
--   (s_strat : Strategy α β)
--   (s_leg: ∀ f_start : Strategy α β , Strategy_legal (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).snd_legal) f_strat s_strat s_strat)
--   -- maybe name this property ? = legal for all strategies ?
--   :
--   let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
--   Strategy_legal g.init_game_state (fun x => g.fst_legal) fst_strat s_strat fst_strat :=
--   by
--   intro fst_strat t
--   induction' t with t ih
--   · dsimp [History_on_turn]
--     rw [if_pos (by rfl)]
--     exact fst_act_legal
--   · dsimp [fst_strat]
--     rw [if_neg _]
--     swap
--     · dsimp [History_on_turn]
--       split_ifs <;> decide
--     · rw [Game_World.world_after_fst_snd_legal] at s_leg
--       sorry


lemma Game_World.History_of_preconditioned
  (g: Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  History_on_turn g.init_game_state fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) ++ [fst_act] :=
  by
  intro fst_strat snd_strat
  induction' turn with t ih
  · dsimp [History_on_turn, Turn_fst]
    rw [if_pos (by decide), if_pos (by rfl)]
  · dsimp only [History_on_turn] at *
    by_cases q : Turn_fst (t+1)
    · rw [Turn_fst_not_step] at q
      rw [if_neg q] at *
      rw [← Turn_fst_not_step] at q
      rw [if_pos q, if_pos q] at *
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Game_World.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]
    · rw [if_neg q, if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q] at *
      rw [if_neg (by apply List.cons_ne_nil)]
      rw [List.cons_append, ← ih]
      congr
      dsimp at ih
      rw [← Game_World.world_after_fst_init] at ih
      rw [ih]
      rw [List.dropLast_concat]


lemma Game_World.fst_of_preconditioned
  (g: Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  fst_strat g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) =
  s_strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) :=
  by
  intro fst_strat snd_strat
  dsimp [fst_strat]
  rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
  have := g.History_of_preconditioned fst_act f_strat s_strat turn
  dsimp at this
  rw [this]
  rw [List.dropLast_concat]



lemma Game_World.snd_of_preconditioned
  (g: Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (turn : ℕ):
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  snd_strat g.init_game_state (History_on_turn g.init_game_state fst_strat snd_strat (turn + 1)) =
  f_strat (g.world_after_fst fst_act).init_game_state (History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat turn) :=
  by
  intro fst_strat snd_strat
  dsimp [fst_strat]
  have := g.History_of_preconditioned fst_act f_strat s_strat turn
  dsimp at this
  rw [this]
  rw [List.dropLast_concat]


#check Game_World.world_after_fst_History

-- lemma Game_World.fst_preconditioned_careless
--   (g: Game_World α β)
--   (fst_act: β)
--   (f_strat s_strat : Strategy α β)
--   (hs : (g.world_after_fst fst_act).Strategy_careless s_strat) (hf : (g.world_after_fst fst_act).Strategy_careless f_strat)
--   (partiallity_hack : fst_act = s_strat (g.world_after_fst fst_act).init_game_state [])
--   -- shouldn't be a problem, as we may s_strat isn't used on empty history
--   (turn : ℕ):
--   let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
--   g.Strategy_careless fst_strat :=
--   by
--   intro fst_strat act hist
--   dsimp
--   by_cases q : hist = []
--   · rw [if_pos q, if_neg (by apply List.append_ne_nil_of_ne_nil_right ; exact List.cons_ne_nil act [])]
--     rw [List.dropLast_concat, q]
--     exact partiallity_hack
--   · dsimp [Strategy_careless] at hs
--     rw [if_neg q, if_neg (by exact List.append_ne_nil_of_left_ne_nil hist [act] q), List.dropLast_concat]
--     rw [hs]
    -- maybe just false ?


--#exit

lemma Game_World.fst_legal_preconditioned
  (g: Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.fst_legal [] fst_act)
  (f_strat s_strat : Strategy α β)
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
  (s_leg: Strategy_legal (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).snd_legal) f_strat s_strat s_strat)
  (partiallity_hack : s_strat g.init_game_state [] = fst_act)
  -- should never be reqiested of s_strat, as its meant to be played on (g.world_after_fst fst_act)
  -- TODO: show that one can assume this wlog on actual games
  (b : g.law_blind_fst s_strat f_strat)
  -- maybe can be derived from g.law_blind_fst fst_strat snd_strat ?
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal g.init_game_state (fun x => g.fst_legal) fst_strat snd_strat fst_strat :=
  by
  intro fst_strat snd_strat t
  induction' t with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · dsimp [fst_strat]
    rw [if_neg _]
    swap
    · dsimp [History_on_turn]
      split_ifs <;> decide
    · have := g.History_of_preconditioned fst_act f_strat s_strat t
      dsimp at this
      rw [this]
      rw [List.dropLast_concat]
      rw [← Game_World.world_after_fst_init]
      rw [← partiallity_hack]
      rw [Game_World.world_after_fst_History]
      · rw [← b]
        rw [partiallity_hack]
        apply s_leg
      · exact hf
      · exact hs


lemma Game_World.snd_legal_preconditioned
  (g: Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy α β)
  (hs : g.Strategy_careless s_strat) (hf : g.Strategy_careless f_strat)
  (f_leg: Strategy_legal (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).fst_legal) f_strat s_strat f_strat)
  (partiallity_hack : s_strat g.init_game_state [] = fst_act)
  -- should never be reqiested of s_strat, as its meant to be played on (g.world_after_fst fst_act)
  -- TODO: show that one can assume this wlog on actual games
  (partiallity_hack' : snd_legal g [] (f_strat (world_after_fst g fst_act).init_game_state []))
  -- again, should be assumed wlog, since this should be the first turn, so the snd law will never be asked to apply
  (b : g.law_blind_snd s_strat f_strat)
  -- maybe can be derived from g.law_blind_snd fst_strat snd_strat ?
  :
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast)) ;
  Strategy_legal g.init_game_state (fun x => g.snd_legal) fst_strat snd_strat snd_strat :=
  by
  intro fst_strat snd_strat t
  induction' t with t ih
  · dsimp [History_on_turn]
    rw [← Game_World.world_after_fst_init]
    exact partiallity_hack'
  · dsimp
    have := g.History_of_preconditioned fst_act f_strat s_strat t
    dsimp at this
    rw [this]
    rw [List.dropLast_concat]
    rw [← Game_World.world_after_fst_init]
    rw [← partiallity_hack]
    rw [Game_World.world_after_fst_History]
    · dsimp [law_blind_snd] at b
      rw [← b]
      rw [partiallity_hack]
      apply f_leg
    · exact hf
    · exact hs



def Game_World.must_terminate_before_wCarelessBlind {α β : Type u} (g : Game_World α β) (T : ℕ): Prop :=
  ∀ f_strat s_strat : Strategy α β,
  (f_law : Strategy_legal g.init_game_state (fun _ => g.fst_legal) f_strat s_strat f_strat) →
  (s_law : Strategy_legal g.init_game_state (fun _ => g.snd_legal) f_strat s_strat s_strat) →
  (hf : g.Strategy_careless f_strat) →
  (hs : g.Strategy_careless s_strat) →
  (hg : g.law_blind f_strat s_strat) →
  let G := ({g with fst_strat := f_strat, fst_lawful := f_law, snd_strat := s_strat, snd_lawful := s_law} : Game α β) ;
  ∃ turn ≤ T,
    ((Turn_fst turn ∧ ∀ act : β, ¬ (G.fst_legal (G.history_on_turn turn) act))
     ∨
     (Turn_snd turn ∧ ∀ act : β, ¬ (G.snd_legal (G.history_on_turn turn) act)))


--#exit

lemma Game_World.world_after_fst_init_must_terminate {α β : Type u} (g : Game_World α β)
  (fst_act : β) (fst_act_legal : g.fst_legal [] fst_act)
  {T : ℕ} :
  g.must_terminate_before_wCarelessBlind (T + 1) → (g.world_after_fst fst_act).must_terminate_before_wCarelessBlind (T) :=
  by
  intro g_bnd
  intro f_strat s_strat f_leg s_leg hf hs hg G
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast))
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (hist.dropLast))
  by_contra! con
  specialize g_bnd fst_strat snd_strat
  sorry


--#exit

-- lemma Game_World.world_after_fst_init_must_playable {α β : Type u} (g : Game_World α β)
--   (f_strat : Strategy α β) :
--   g.playable_snd → (g.world_after_fst (f_strat g.init_game_state [])).playable_fst :=
--   by
--   intro hp
--   obtain ⟨s, s_prop ⟩ := hp
--   use s
--   use f_strat
--   constructor
--   · apply Game_World.world_after_snd_legal


  -- first strat would be second init strat with fst move the reaction to init fst strat


-- # New approach here

def Strategy_legal_in_pair {α β : Type u}
  (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat s_strat : Strategy α β): Prop :=
  ∀ turn : ℕ, (f_law ini (History_on_turn ini f_strat s_strat turn) (f_strat ini (History_on_turn ini f_strat s_strat turn)))
    ∧ (s_law ini (History_on_turn ini f_strat s_strat turn) (s_strat ini (History_on_turn ini f_strat s_strat turn)))

lemma Game_World.legal_copy {α β : Type u} (g : Game_World α β)
  (fst_act : β) (fst_act_legal : g.fst_legal [] fst_act)
  (f_strat s_strat : Strategy α β)
  (f_leg: Strategy_legal (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).fst_legal) f_strat s_strat f_strat)
  (s_leg: Strategy_legal (g.world_after_fst fst_act).init_game_state (fun x => (g.world_after_fst fst_act).snd_legal) f_strat s_strat s_strat)
  (hg : g.law_blind f_strat s_strat) :
  let H := History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (H (hist.length - 1)))
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (H (hist.length - 1)))
  Strategy_legal_in_pair g.init_game_state (fun _ => g.fst_legal) (fun _ => g.snd_legal) fst_strat snd_strat :=
  by
  intro H fst_strat snd_strat t
  induction' t with t ih
  · dsimp [History_on_turn]
    rw [if_pos (by rfl)]
    exact fst_act_legal
  · dsimp [fst_strat]
    rw [if_neg (by apply History_on_turn_nonempty_of_succ)]



lemma Game_World.world_after_fst_init_must_terminate' {α β : Type u} (g : Game_World α β)
  (fst_act : β) (fst_act_legal : g.fst_legal [] fst_act)
  {T : ℕ} :
  g.must_terminate_before (T + 1) → (g.world_after_fst fst_act).must_terminate_before (T) :=
  by
  intro g_bnd
  intro f_strat s_strat f_law s_law G
  let H := History_on_turn (g.world_after_fst fst_act).init_game_state f_strat s_strat
  let fst_strat : Strategy α β := (fun ini hist => if hist = [] then fst_act else s_strat (g.world_after_fst fst_act).init_game_state (H (hist.length - 1)))
  let snd_strat : Strategy α β := (fun ini hist => f_strat (g.world_after_fst fst_act).init_game_state (H (hist.length - 1)))
  by_contra! con
  specialize g_bnd fst_strat snd_strat
  sorry


#exit

lemma Game_World.conditioning {α β : Type u}
  (g : Game_World α β)
  --(hp : g.playable') (hpU : ∀ f_act, (g.world_after_fst f_act).playable') -- can we weaken this ?
  -- probably not ? One can think of an f_act that causes the second player to have no legal moves
  -- on the second round already. The game would still be playble, but the first player
  -- has to avoid f_act.
  {T : ℕ} (hg : g.must_terminate_before T)
  {P : Game_World α β → Prop}
  (step : ∀ (g' : Game_World α β), (∀ (f_strat : Strategy α β), P (g'.world_after_fst (f_strat g'.init_game_state []))) → P g')
  (base : ∀ (g' : Game_World α β), g'.must_terminate_before 0 → P g')
  :
  P g :=
  by
  revert g
  induction' T with T ih
  · apply base
  · intro g gt
    apply step
    intro f_strat
    apply ih
  -- · intro g hp hpU hg
  --   obtain ⟨f, s, f_prop, s_prop ⟩ := hp
  --   dsimp [Game_World.must_terminate_before] at hg
  --   specialize hg f s (f_prop) (s_prop)
  --   obtain ⟨z,zz, z_prop⟩ := hg
  --   rw [Nat.le_zero] at zz
  --   rw [zz] at z_prop
  --   cases' z_prop with l r
  --   · rw [Turn_fst] at l ; obtain ⟨ahh, b⟩ := l ; contradiction
  --   · specialize s_prop
  --     rw [Strategy_legal] at s_prop
  --     specialize s_prop 0
  --     exfalso
  --     exact (r.2 (s g.init_game_state (History_on_turn g.init_game_state f s 0))) s_prop
  -- · intro g hp hpU hg
  --   apply ch
  --   intro f_act
  --   apply ih



#exit

theorem Game_World.Zermelo {α β : Type u} (g : Game_World α β)
            (hp : g.playable)
            {T : ℕ} (hg : g.must_terminate_before T) :
            g.has_win_loose_draw_strat :=
  by
  revert g
  induction' T with max_turn ih
  · intro g hp hg
    obtain ⟨⟨f, f_prop ⟩,⟨s, s_prop ⟩⟩ := hp
    dsimp [Game_World.must_terminate_before] at hg
    specialize hg f s (f_prop s) (s_prop f)
    obtain ⟨z,zz, z_prop⟩ := hg
    rw [Nat.le_zero] at zz
    rw [zz] at z_prop
    cases' z_prop with l r
    · rw [Turn_fst] at l ; obtain ⟨ahh, b⟩ := l ; contradiction
    · specialize s_prop f
      rw [Strategy_legal] at s_prop
      specialize s_prop 0
      exfalso
      exact (r.2 (s g.init_game_state (History_on_turn g.init_game_state f s 0))) s_prop
  · intro g hp hg

-- do a by cases

-- show that g.world_after_fst are playable
-- show that g.world_after_fst must terminate bofre max_t
-- show that if g.world_after_fst is wld, the so is g
