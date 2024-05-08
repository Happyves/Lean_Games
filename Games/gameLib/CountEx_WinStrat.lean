/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic
import Games.gameLib.Termination
import Games.exLib.List


def problem_1 : Symm_Game_World ℕ ℕ where
  init_game_state := 42
  win_states := fun x => x = 0
  transition := fun _ _ _ => 37
  law := fun _ _ _  => False


example : ∃ g : Symm_Game_World ℕ ℕ, g.is_fst_win ∧
  (∀ f_strat s_strat : Strategy ℕ ℕ, ¬ Strategy_legal_fst g.init_game_state g.law f_strat s_strat) :=
  by
  use problem_1
  constructor
  · use (fun _ _ => 666)
    intro _ nope
    exfalso
    dsimp [problem_1] at nope
    specialize nope 0 (by decide)
    exact nope
  · intro _ _
    dsimp [problem_1]
    intro con
    specialize con 0 (by decide)
    exact con


def Symm_Game_World.is_snd_win_ALT_1  {α β : Type u} (g : Symm_Game_World α β) : Prop :=
  ∃ ws : Strategy α β,
  ∀ fst_s : Strategy α β,
   ∃ (ws_leg : Strategy_legal_snd g.init_game_state g.law fst_s ws),
   ∃ (fst_leg : Strategy_legal_fst g.init_game_state g.law fst_s ws ),
  ({g with fst_strat := fst_s, fst_lawful := fst_leg, snd_strat := ws, snd_lawful := ws_leg} : Symm_Game α β).snd_win


example : ∀ g : Symm_Game_World α β, (∃ hist : List β, ∃ act : β, ¬ g.law g.init_game_state hist act) →  ¬ g.is_snd_win_ALT_1 :=
  by
  intro g plausible con
  obtain ⟨Hist, Act, plausible⟩ := plausible
  -- use List.exists_min_length_list_of_exists_list
