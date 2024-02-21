/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Positional


def Game_World.has_pairing {γ : Type} -- else I get universe error
  (g : Game_World (γ → Fin 3) β) : Prop :=
  ∀ s : (γ → Fin 3), g.fst_win_states s → ∃ i j : γ, i ≠ j ∧ s i = 1 ∧ s j = 1

/-
all wining states of the first player require him claiming two tiles (depending on the winning state).
If γ is finite, the second player can claim one element from each pair, so that the fst winning
states can never be reached
....
hmmmmmmm
-/

theorem Game_World.has_pairing_is_snd_draw
  (g : Game_World (γ → Fin 3) β)
  (hp : g.has_pairing) (hp : g.must_terminate)
  (hlf : g.fst_legal = fun hist act => act ∉ hist) -- add pos game transition too ?
  (hls : g.snd_legal = fun hist act => act ∉ hist) :
  g.is_snd_draw :=
  by
  sorry


def Positional_Game_World.has_pairing (win_sets : Finset (Finset α)) :=
  ∃ p : (w : Finset α) → (hw : w ∈ win_sets) → (α × α),
    ∀ w : Finset α, (hw : w ∈ win_sets) →
      ((p w hw).1 ≠ (p w hw).2) ∧
      ( ∀ v : Finset α, (hv : v ∈ win_sets) → v ≠ w →
          ((p w hw).1 ≠ (p v hv).1) ∧ ((p w hw).2 ≠ (p v hv).2)
          ∧ (p w hw).1 ≠ (p v hv).2 ∧ ((p w hw).2 ≠ (p v hv).1))
 -- parwise distict [(p w hw).1, (p v hv).1, (p w hw).2, (p v hv).2] ?
