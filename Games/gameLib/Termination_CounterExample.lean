/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Mathlib.Tactic


-- infinite chomp ; we may find aribrtarily long games
example : ∃ α β : Type, ∃ g : Symm_Game_World α β,
            g.must_terminate ∧
            (∀ T : ℕ, ¬ g.must_terminate_before T) :=
