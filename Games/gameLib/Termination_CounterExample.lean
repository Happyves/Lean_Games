/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.games.Chomp
import Mathlib.Tactic


-- use 1-dim version for ease of expo

def InfiChomp : Symm_Game_World (List (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := []
  win_states := (fun l => ∀ p : ℕ × ℕ, (∀ q ∈ l, nondomi q p) → p = (0,0))
  transition := fun h a => a :: h
  law := fun hist act => ∀ q ∈ hist, nondomi q act

-- infinite chomp ; we may find aribrtarily long games
example : ∃ α β : Type, ∃ g : Symm_Game_World α β,
            g.must_terminate ∧
            (∀ T : ℕ, ¬ g.must_terminate_before T) :=
