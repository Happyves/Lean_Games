/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.Nat
import Games.gameLib.Basic
import Mathlib.Tactic


def domi (p q : ℕ × ℕ) : Prop := p.1 ≤ q.1 ∧ p.2 ≤ q.2

def nondomi (p q : ℕ × ℕ) : Prop := ¬ domi p q

instance : DecidableRel domi :=
  by
  intro p q
  rw [domi]
  exact And.decidable

instance : DecidableRel nondomi :=
  by
  intro p q
  rw [nondomi]
  exact Not.decidable


variable {height length : ℕ}

structure Chomp_law (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  h : act.2 ≤ height
  l : act.1 ≤ length
  nd : ∀ q ∈ hist, nondomi q act

/--
State is basicly hist : it collects the places where a player has chomped
the board. Initially, nothing was chomped. We transition by adding moves.
-/
def Chomp : Symm_Game_World (List (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := []
  win_states := (fun l => ∀ p : ℕ × ℕ, (∀ q ∈ l, nondomi q p) → p = (0,0))
  transition := fun h a => a :: h
  law := @Chomp_law height length


instance (l : List (ℕ × ℕ)) : DecidablePred (fun p => ∀ q ∈ l, nondomi q p) :=
  by
  intro p
  dsimp [nondomi,domi]
  exact List.decidableBAll (fun x => ¬(x.1 ≤ p.1 ∧ x.2 ≤ p.2)) l

-- pretty print the state
def pp_Chomp_state (l : List (ℕ × ℕ)) :=
  (List.product (List.range (length +1)) (List.range (height +1))).filter
    (fun p => ∀ q ∈ l, nondomi q p)
