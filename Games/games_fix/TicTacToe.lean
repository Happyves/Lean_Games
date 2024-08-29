/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Pairing


variable (D n : ℕ)

inductive in_de_const (s : Fin n → Fin n) : Prop
| cst : (∃ x : Fin n, ∀ i : Fin n, s i = x) → in_de_const s
| inc : (∀ i : Fin n, s i = i) → in_de_const s
| dec : (∀ i : Fin n, s i = n - 1 - i) → in_de_const s


structure seq_is_line (s : Fin n → (Fin D → Fin n)) : Prop where
  idc : ∀ d : Fin D, in_de_const n (fun j : Fin n => (s j) d)
  non_pt : ¬ (∀ d : Fin D, (∃ x : Fin n, ∀ j : Fin n, s j d = x))


def is_combi_line (can : Finset (Fin D → Fin n)) : Prop :=
  ∃ s : Fin n → (Fin D → Fin n), seq_is_line D n s ∧ can = Finset.image s .univ


open Classical

noncomputable
def TTT_win_sets : Finset (Finset (Fin D → Fin n)) := Finset.univ.filter (is_combi_line D n)

noncomputable
def TTT := Positional_Game_World (TTT_win_sets D n)
