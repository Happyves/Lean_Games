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
