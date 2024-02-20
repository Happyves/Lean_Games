/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic


variable (D n : ℕ)

inductive in_de_const (s : Fin n → Fin n) : Prop
| cst : (∃ x : Fin n, ∀ i : Fin n, s i = x) → in_de_const s
| inc : (∀ i : Fin n, s i = i) → in_de_const s
| dec : (∀ i : Fin n, s i = n - 1 - i) → in_de_const s


structure seq_is_line (s : Fin n → (Fin D → Fin n)) : Prop where
  idc : ∀ d : Fin D, in_de_const n (fun j : Fin n => (s j) d)
  non_pt : ¬ (∀ d : Fin D, (∃ x : Fin n, ∀ j : Fin n, s j d = x))


def has_x_line (state : ((Fin D → Fin n) → Fin 3)) : Prop :=
  ∃ l : Fin n → (Fin D → Fin n), (seq_is_line D n l) ∧ (∀ i : Fin n, state (l i) = 1)


def has_o_line (state : ((Fin D → Fin n) → Fin 3)) : Prop :=
  ∃ l : Fin n → (Fin D → Fin n), (seq_is_line D n l) ∧ (∀ i : Fin n, state (l i) = 2)


def TTT_fst_trans (hist : List (Fin D → Fin n)) (act : (Fin D → Fin n)) : (Fin D → Fin n) → Fin 3 :=
  fun p => if h1 : p = act
           then 1
           else if h2 : p ∈ hist
                then if h2a : Turn_fst (hist.indexOf p)
                     then 1
                     else 2
                else 0

def TTT_snd_trans (hist : List (Fin D → Fin n)) (act : (Fin D → Fin n)) : (Fin D → Fin n) → Fin 3 :=
  fun p => if h1 : p = act
           then 2
           else if h2 : p ∈ hist
                then if h2a : Turn_fst (hist.indexOf p)
                     then 1
                     else 2
                else 0


def TTT_legal (hist : List (Fin D → Fin n)) (act : (Fin D → Fin n)) : Prop := act ∉ hist


def TTT : Game_World ((Fin D → Fin n) → Fin 3) (Fin D → Fin n) where
  init_game_state := fun _ => 0
  fst_win_states := fun s => has_x_line D n s
  fst_transition := TTT_fst_trans D n
  fst_legal := TTT_legal D n
  snd_win_states := fun s => has_o_line D n s
  snd_transition := TTT_snd_trans D n
  snd_legal := TTT_legal D n
