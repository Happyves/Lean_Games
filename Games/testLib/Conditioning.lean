/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Games.testLib.Basic



def Symm_Game_World.world_after_fst {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : Symm_Game_World α β := -- act not required to be legal
  {g with init_game_state := g.transition [] fst_act }


@[simp]
lemma Symm_Game_World.world_after_fst_init {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.transition [] fst_act :=
  by rfl

@[simp]
lemma Symm_Game_World.world_after_fst_law {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).law = g.law :=
  by rfl

@[simp]
lemma Game_World_wDraw.world_after_fst_win_states {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).win_states = g.win_states :=
  by rfl

@[simp]
lemma Symm_Game_World.world_after_fst_draw_states {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).draw_states = g.draw_states :=
  by rfl

@[simp]
lemma Symm_Game_World.world_after_fst_transition {α β : Type u} (g : Symm_Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).transition = g.transition :=
  by rfl


-- # Coherent end

structure Symm_Game_World.coherent_end_aux
  (g : Symm_Game_World α β) (f_strat s_strat : Strategy g) (t : ℕ) : Prop where
  f : g.win_states (g.state_on_turn f_strat s_strat t) → g.win_states (g.state_on_turn f_strat s_strat (t+1))
  d : g.draw_states (g.state_on_turn f_strat s_strat t) → g.draw_states (g.state_on_turn f_strat s_strat (t+1))

def Symm_Game_World.coherent_end (g : Symm_Game_World α β) : Prop :=
  ∀ f_strat s_strat : Strategy g, ∀ t : ℕ, g.coherent_end_aux f_strat s_strat t


structure zSymm_Game_World (α β : Type _) extends Symm_Game_World α β where
  coherent : toSymm_Game_World.coherent_end


instance (l : List α): Decidable (l = []) :=
  by
  match l with
  | [] => apply isTrue ; rfl
  | x :: L => apply isFalse ; exact List.cons_ne_nil x L


def fst_strat_deconditioned (g : Symm_Game_World α β) (s_strat : Strategy g) (f_act : β): Strategy g :=
  (fun hist => if hist = [] then f_act else s_strat  (hist.dropLast))

def snd_strat_deconditioned (g : Symm_Game_World α β) (f_strat : Strategy g) : Strategy g :=
  (fun hist => f_strat (hist.dropLast))


lemma Symm_Game_World.History_of_deconditioned
  (g: Symm_Game_World α β)
  (fst_act: β)
  (f_strat s_strat : Strategy g)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned g s_strat fst_act
  let snd_strat := snd_strat_deconditioned g f_strat
  History_on_turn g fst_strat snd_strat (turn + 1) =
  (History_on_turn (g.world_after_fst fst_act) f_strat s_strat turn) ++ [fst_act] :=
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
      rw [ih]
      rw [snd_strat_deconditioned, List.dropLast_concat]
    · rw [if_neg q, if_neg q] at *
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q] at *
      rw [fst_strat_deconditioned, snd_strat_deconditioned, if_neg (by apply List.cons_ne_nil)]
      rw [List.cons_append, ← ih]
      congr
      dsimp [snd_strat_deconditioned] at ih
      rw [ih]
      rw [List.dropLast_concat]


lemma Symm_Game_World.State_of_deconditioned
  (g: Symm_Game_World α β)
  (fst_act: β)
  (fst_act_legal: g.law [] fst_act)
  (f_strat s_strat : Strategy g)
  (turn : ℕ):
  let fst_strat := fst_strat_deconditioned g s_strat fst_act
  let snd_strat := snd_strat_deconditioned g f_strat
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
      simp_rw [this]
      rw [snd_strat_deconditioned, List.dropLast_concat]
      rw [← this]
      clear this
      dsimp [fst_strat_deconditioned]
      dsimp at this
      specialize this t (f_strat (world_after_fst g fst_act).toGame_World.init_game_state (History_on_turn (world_after_fst g fst_act).toGame_World.init_game_state f_strat s_strat t))
      rw [← Game_World_wDraw.world_after_fst_init]
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
      specialize this t (s_strat (world_after_fst g fst_act).toGame_World.init_game_state (History_on_turn (Game_World.fst_transition g.toGame_World g.init_game_state [] fst_act) f_strat s_strat t))
      rw [← Game_World_wDraw.world_after_fst_init] at this
      rw [← Game_World_wDraw.world_after_fst_init]
      rw [← this]
