/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Positional



structure Game_World.pairing_prop_pairdiff_fst
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (w' v : (γ → Fin 3))
  (hw' : fst_win_states g w')
  (hv : fst_win_states g v)
  : Prop where
  d2 : (p w' hw).1 ≠ (p v hv).1
  d3 : (p w' hw).2 ≠ (p v hv).2
  d4 : (p w' hw).1 ≠ (p v hv).2
  d5 : (p w' hw).2 ≠ (p v hv).1

structure Game_World.pairing_prop_fst
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (w' : (γ → Fin 3))
  (hw' : fst_win_states g w')
  : Prop where
  d : (p w' hw').1 ≠ (p w' hw').2
  ff : (w' (p w' hw').1 = 1)
  sf : (w' (p w' hw').2 = 1)


def Game_World.pairing_fst
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))  : Prop :=
    (∀ (w' : (γ → Fin 3)), (hw' : g.fst_win_states w') →
      ( g.pairing_prop_fst p w' hw' ∧
        (∀ (v : (γ → Fin 3)), (hv : g.fst_win_states v) → v ≠ w' →
          g.pairing_prop_pairdiff_fst p w' v hw' hv)))


def Game_World.has_pairing_fst
  (g : Game_World (γ → Fin 3) γ) : Prop :=
  ∃ p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ),
    g.pairing_fst p

def Game_World.pairing_pairs
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ)) :
  Set γ :=
  {pts : γ | ∃ s : (γ → Fin 3), ∃ hw : g.fst_win_states s,  pts = (p s hw).1 ∨ pts = (p s hw).2}

open Classical

noncomputable
def Game_World.snd_pairing_strat
  [Inhabited γ]
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (hp : g.pairing_fst p) : Strategy (γ → Fin 3) γ :=
  fun ini hist =>
    match hist with
    | [] => default
    | prev :: h => if h_mem : prev ∈ g.pairing_pairs p
                   then (show γ from (
                      by
                      dsimp [Game_World.pairing_pairs] at h_mem
                      choose s hw prop using h_mem
                      -- cases' prop with
                      -- · sorry -- expected checkColGt
                      -- · sorry
                      by_cases q :  prev = (p s hw).1 -- if prev is fst of pair
                      · by_cases k : ∃ a : γ, a ∉ (prev :: h) -- if there are tiles left
                        · by_cases K : (p s hw).2 ∉ (prev :: h) -- if the second of pair isn't taken
                          · exact (p s hw).2 --then select second of pair
                          · choose a _ using k -- else chose some available tile
                            exact a
                        · exact default -- should never occur
                      · rw [or_iff_right q] at prop
                        exact (p s hw).1 -- else choose first tile

                   ))
                   else (show γ from (
                          by
                          by_cases k : ∃ a : γ, a ∉ (prev :: h)
                          · choose a _ using k
                            exact a
                          · exact default
                   ))

#print Game_World.snd_pairing_strat


theorem Game_World.has_pairing_is_snd_draw
  (g : Game_World (γ → Fin 3) γ)
  (hp : g.has_pairing_fst)
  {T : ℕ} (ht : g.must_terminate_before T)
  (hlf : g.fst_legal = fun hist act => act ∉ hist) -- add pos game transition too ?
  (hls : g.snd_legal = fun hist act => act ∉ hist) :
  g.is_snd_win ∨ g.is_snd_draw :=
  by
  sorry


structure pairing_prop_aux
  (win_sets : Finset (Finset α))
  (p : (w : Finset α) → (hw : w ∈ win_sets) → (α × α))
  (w' v : Finset α)
  (hw : w' ∈ win_sets)
  (hv : v ∈ win_sets)
  : Prop where
  d2 : (p w' hw).1 ≠ (p v hv).1
  d3 : (p w' hw).2 ≠ (p v hv).2
  d4 : (p w' hw).1 ≠ (p v hv).2
  d5 : (p w' hw).2 ≠ (p v hv).1


def Positional_Game_World.has_pairing (win_sets : Finset (Finset α)) :=
  ∃ p : (w : Finset α) → (hw : w ∈ win_sets) → (α × α),
    ∀ w' : Finset α, (hw : w' ∈ win_sets) →
      ((p w' hw).1 ≠ (p w' hw).2) ∧
      (∀ v : Finset α, (hv : v ∈ win_sets) → v ≠ w' →
          pairing_prop_aux win_sets p w' v hw hv)
