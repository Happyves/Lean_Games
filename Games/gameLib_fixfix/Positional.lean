/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Termination


def PosGame_trans [DecidableEq α] (hist : List α) : α → Fin 3 :=
  fun p => if  p ∈ hist
           then if Turn_fst (hist.indexOf p)
                then 1
                else 2
           else 0


open Classical

def Positional_Game_World [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : Game_World_wDraw (α → Fin 3) α where
     init_game_state := fun _ => 0
     fst_transition := fun _ hist act => PosGame_trans (act :: hist)
     snd_transition := fun _ hist act => PosGame_trans (act :: hist)
     fst_win_states := fun ini hist => (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ)
     snd_win_states := fun ini hist => (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ)
     draw_states := fun ini hist => ∀ p : α, (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0
     fst_legal := fun ini hist act =>
                    if State_from_history_neutral_wDraw ini -- for ↓ don't know why field names not accepted ... might be fixed when updating
                         (fun ini hist => (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ))
                         (fun ini hist => (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ))
                         (fun ini hist => ∀ p : α, (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0)
                         hist
                    then act ∉ hist
                    else True
     snd_legal := fun ini hist act =>
                    if State_from_history_neutral_wDraw ini -- for ↓ don't know why field names not accepted ... might be fixed when updating
                         (fun ini hist => (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ))
                         (fun ini hist => (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ))
                         (fun ini hist => ∀ p : α, (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0)
                         hist
                    then act ∉ hist
                    else True


lemma Positional_Game_World_mem_state [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (p : α) (hist : List α) (h : p ∈ hist) :
     (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition hist) p ≠ 0 :=
     by
     cases' hist with x _
     · contradiction
     · dsimp [State_from_history, Positional_Game_World]
       rw [ite_self]
       dsimp [PosGame_trans]
       rw [if_pos h]
       split_ifs
       all_goals {decide}



lemma Positional_Game_World_playable [Inhabited α] [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : (Positional_Game_World win_sets).playable :=
     by
     intro hist _
     constructor
     · intro _
       by_cases N : State_from_history_neutral_wDraw (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_win_states (Positional_Game_World win_sets).snd_win_states (Positional_Game_World win_sets).draw_states hist
       · dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         simp_rw [if_pos N]
         dsimp [State_from_history_neutral_wDraw] at N
         replace N := N.2.2
         push_neg at N
         obtain ⟨p,pp⟩ := N
         use p
         contrapose! pp
         apply Positional_Game_World_mem_state win_sets p hist pp
       · use default
         dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         rw [if_neg N]
         apply True.intro
     · intro _
       by_cases N : State_from_history_neutral_wDraw (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_win_states (Positional_Game_World win_sets).snd_win_states (Positional_Game_World win_sets).draw_states hist
       · dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         simp_rw [if_pos N]
         dsimp [State_from_history_neutral_wDraw] at N
         replace N := N.2.2
         push_neg at N
         obtain ⟨p,pp⟩ := N
         use p
         contrapose! pp
         apply Positional_Game_World_mem_state win_sets p hist pp
       · use default
         dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         rw [if_neg N]
         apply True.intro





lemma Positional_Game_World.decreasing_neutral [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (hist : List α) (act : α) :
  let g := Positional_Game_World win_sets
  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist)) x = 0) Finset.univ
  ⊆ Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (hist)) x = 0) Finset.univ :=
  by
  intro g
  intro x
  simp_rw [Finset.mem_filter]
  rintro ⟨_,xdef⟩
  refine' ⟨Finset.mem_univ _, _ ⟩
  dsimp [State_from_history, Positional_Game_World] at xdef
  rw [ite_self] at xdef
  cases' hist with y l
  · dsimp [State_from_history, Positional_Game_World]
  · dsimp [State_from_history, Positional_Game_World]
    rw [ite_self]
    dsimp [PosGame_trans] at *
    split_ifs at xdef
    · contradiction
    · contradiction
    · rename_i main
      rw [if_neg (by contrapose! main ; exact List.Mem.tail act main)]




lemma Positional_Game_World.strict_decreasing_neutral [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (hist : List α) (act : α) :
  let g := Positional_Game_World win_sets ;
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.fst_win_states g.draw_states hist →
  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist)) x = 0) Finset.univ
  ⊂ Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (hist)) x = 0) Finset.univ :=
  by sorry

#check Finset.ssubset_iff_of_subset
#check Finset.ssubset_iff_subset_ne
