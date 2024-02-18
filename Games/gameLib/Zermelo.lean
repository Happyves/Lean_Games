/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Mathlib.Tactic


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


def Game_World.world_after_fst {α β : Type u} (g : Game_World α β)
  (fst_act : β) : Game_World α β := -- act not required to be legal
  {g with init_game_state := g.fst_transition [] fst_act }

lemma Game_World.world_after_fst_init {α β : Type u} (g : Game_World α β)
  (fst_act : β) : (g.world_after_fst fst_act).init_game_state = g.fst_transition [] fst_act :=
  by rfl

lemma Game_World.conditioning {α β : Type u}
  (g : Game_World α β) (hp : g.playable)
  {P : Game_World α β → Prop}
  (ch : ∀ (fst_act : β) (fst_act_legal : g.fst_legal [] fst_act), P (g.world_after_fst fst_act)) :
  P g :=
  by
  sorry


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
