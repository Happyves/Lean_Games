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


def has_x_line (state : ((Fin D → Fin n) → Fin 3)) : Prop :=
  ∃ l : Fin n → (Fin D → Fin n), (seq_is_line D n l) ∧ (∀ i : Fin n, state (l i) = 1)


def has_o_line (state : ((Fin D → Fin n) → Fin 3)) : Prop :=
  ∃ l : Fin n → (Fin D → Fin n), (seq_is_line D n l) ∧ (∀ i : Fin n, state (l i) = 2)


def is_combi_line (can : Finset (Fin D → Fin n)) : Prop :=
  ∃ s : Fin n → (Fin D → Fin n), seq_is_line D n s ∧ can = Finset.image s .univ


open Classical

noncomputable
def TTT_win_sets : Finset (Finset (Fin D → Fin n)) := Finset.univ.filter (is_combi_line D n)



def TTT_draw (hist : List (Fin D → Fin n)) : Prop :=
  ∀ p : Fin D → Fin n, (State_from_history (fun _ => 0) (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0

def TTT_legal (hist : List (Fin D → Fin n)) (act : (Fin D → Fin n)) : Prop := ¬ TTT_draw D n hist → act ∉ hist


def preTTT : Game_World_wDraw ((Fin D → Fin n) → Fin 3) (Fin D → Fin n) where
  init_game_state := fun _ => 0
  fst_win_states := fun ini hist => Turn_fst (hist.length + 1) ∧ has_x_line D n (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist)
  snd_win_states := fun ini hist => Turn_snd (hist.length + 1) ∧ has_o_line D n (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist)
  fst_legal := fun _ => TTT_legal D n
  snd_legal := fun _ => TTT_legal D n
  fst_transition := fun _ hist act => PosGame_trans (act :: hist)
  snd_transition := fun _ hist act => PosGame_trans (act :: hist)
  draw_states := fun _ => TTT_draw D n

def TTT : Positional_Game_World (TTT_win_sets D n) where
  toGame_World_wDraw := preTTT D n
  init_scheme := rfl
  fst_win_states_scheme :=
    by
    intro hist _
    dsimp [preTTT]
    simp only [and_congr_right_iff]
    intro _
    dsimp [has_x_line, TTT_win_sets] -- is_combi_line
    simp_rw [Finset.mem_filter, is_combi_line]
    constructor
    · rintro ⟨s ,sdef, W⟩
      use Finset.image s Finset.univ
      constructor
      · constructor
        · exact Finset.mem_univ (Finset.image s Finset.univ)
        · exact Exists.intro s { left := sdef, right := rfl }
      · intro x
        rw [Finset.mem_image, Finset.mem_filter]
        rintro ⟨a,_, adef⟩
        constructor
        · exact Finset.mem_univ x
        · rw [← adef]
          exact W a
    · rintro ⟨w,⟨ _, ⟨s,sdef,sw⟩⟩,wsub⟩
      refine' ⟨s,sdef,_⟩
      intro i
      have iw : s i ∈ w :=
        by
        rw [sw, Finset.mem_image]
        use i
        exact ⟨Finset.mem_univ  _ , rfl⟩
      replace wsub := wsub iw
      rw [Finset.mem_filter] at wsub
      exact wsub.2
  snd_win_states_scheme :=
    by
    intro hist _
    dsimp [preTTT]
    simp only [and_congr_right_iff]
    intro _
    dsimp [has_x_line, TTT_win_sets] -- is_combi_line
    simp_rw [Finset.mem_filter, is_combi_line]
    constructor
    · rintro ⟨s ,sdef, W⟩
      use Finset.image s Finset.univ
      constructor
      · constructor
        · exact Finset.mem_univ (Finset.image s Finset.univ)
        · exact Exists.intro s { left := sdef, right := rfl }
      · intro x
        rw [Finset.mem_image, Finset.mem_filter]
        rintro ⟨a,_, adef⟩
        constructor
        · exact Finset.mem_univ x
        · rw [← adef]
          exact W a
    · rintro ⟨w,⟨ _, ⟨s,sdef,sw⟩⟩,wsub⟩
      refine' ⟨s,sdef,_⟩
      intro i
      have iw : s i ∈ w :=
        by
        rw [sw, Finset.mem_image]
        use i
        exact ⟨Finset.mem_univ  _ , rfl⟩
      replace wsub := wsub iw
      rw [Finset.mem_filter] at wsub
      exact wsub.2
  legal_condition :=
    by
    intro hist act leg N
    cases' leg
    rename_i now
    rw [preTTT, ite_self] at now
    dsimp at now
    apply now
    dsimp [State_from_history_neutral_wDraw, preTTT] at N
    exact N.2.2
  transition_scheme :=
    by
    intro hist leg
    induction' hist with x l ih
    · dsimp [State_from_history, preTTT]
      funext y
      rw [PosGame_trans, if_neg (by exact List.not_mem_nil y)]
    · cases' leg
      rename_i sofar now
      specialize ih sofar
      dsimp [State_from_history, preTTT]
      funext y
      rw [ite_self]
