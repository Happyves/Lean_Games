/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Positional






structure pairProp {win_sets : Finset (Finset α)} (win_set : win_sets) (p : α × α) : Prop where
  dif : p.1 ≠ p.2
  mem_fst : p.1 ∈ win_set.val
  mem_snd : p.2 ∈ win_set.val


structure pairDif (a b : α × α) : Prop where
  strait_fst : a.1 ≠ b.1
  strait_snd : a.2 ≠ b.2
  cross_fst : a.1 ≠ b.2
  cross_snd : a.2 ≠ b.1

structure Pairing_condition [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (pairing : win_sets → (α × α)) where
  has_pairing : ∀ w : win_sets, pairProp w (pairing w)
  pairing_dif : ∀ w v : win_sets, w ≠ v → pairDif (pairing w) (pairing v)



noncomputable
def Pairing_StratCore [Inhabited α] [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (pairing : win_sets → (α × α)) :
  (hist : List α) → (leg : Hist_legal (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_legal (Positional_Game_World win_sets).snd_legal hist) → α :=
  fun hist leg =>
    let spam :=
      if T : Turn_fst (hist.length + 1)
            then
              Classical.choose (((Positional_Game_World_playable win_sets) hist (leg)).1 T)
            else
              Classical.choose (((Positional_Game_World_playable win_sets) hist (leg)).2 (by rw [Turn_snd_iff_not_fst] ; exact T))
    match hist with
    | last :: _ =>
        if hxf : ∃ w : win_sets, last = (pairing w).1
        then
          let other := (pairing (Classical.choose hxf)).2
          if other ∈ hist
          then spam
          else other
        else
          if hxs : ∃ w : win_sets, last = (pairing w).2
          then
            let other := (pairing (Classical.choose hxs)).1
            if other ∈ hist
            then spam
            else other
          else
            spam
    | [] => spam




noncomputable
def Pairing_fStrat [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (pairing : win_sets → (α × α)):
  fStrategy (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_legal (Positional_Game_World win_sets).snd_legal :=
  fun hist T leg =>
    ⟨ Pairing_StratCore win_sets pairing hist leg,
      (by
       dsimp [Positional_Game_World]
       split_ifs with N
       cases' hist with last L
       · dsimp [Pairing_StratCore]
         rw [dif_pos (by decide)]
         apply List.not_mem_nil
       · dsimp [Pairing_StratCore]
         by_cases hxf : ∃ w : win_sets, last = (pairing w).1
         · rw [dif_pos hxf]
           split_ifs with M
           · have := Classical.choose_spec (Pairing_StratCore.proof_1 win_sets (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · have := Classical.choose_spec (Pairing_StratCore.proof_1 win_sets (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · exact M
         · rw [dif_neg hxf]
           by_cases hxs : ∃ w : win_sets, last = (pairing w).2
           · rw [dif_pos hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · exact M
           · rw [dif_neg hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
       )
      ⟩


noncomputable
def Pairing_sStrat [Inhabited α] [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (pairing : win_sets → (α × α)) :
  sStrategy (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_legal (Positional_Game_World win_sets).snd_legal :=
  fun hist T leg =>
    ⟨ Pairing_StratCore win_sets pairing hist leg,
      (by
       dsimp [Positional_Game_World]
       split_ifs with N
       cases' hist with last L
       · dsimp [Pairing_StratCore]
         rw [dif_pos (by decide)]
         apply List.not_mem_nil
       · dsimp [Pairing_StratCore]
         by_cases hxf : ∃ w : win_sets, last = (pairing w).1
         · rw [dif_pos hxf]
           split_ifs with M
           · have := Classical.choose_spec (Pairing_StratCore.proof_2 win_sets (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · have := Classical.choose_spec (Pairing_StratCore.proof_2 win_sets (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · exact M
         · rw [dif_neg hxf]
           by_cases hxs : ∃ w : win_sets, last = (pairing w).2
           · rw [dif_pos hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · exact M
           · rw [dif_neg hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 win_sets (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
       )
      ⟩


/-
- Show that the size preimage under `State_from_history` of α of 0 (aka non claimed tiles) decreases at each turn that is neutral (should be true in any positional game)
- show that the set of turns that are neutral is upperbounded by Fintype.card α
- Argue with finitenenss of decreasing sequence of nats (Fintype.card α - t), cause API for maximum doesn't seem to exist ; maybe write that API
  Alternatively, argue over infiteness ? derive not infinite via upperbound  and the use finset amximum API ?
- disjoin on turn after last neutral turn : if its a draw or snd_win, we've got the theorem
- show that it can't be a first win as follows:
  - if it were, there'd be a monochromatic win set
  - for that win set, consider the first turn such that one of the paring elems was colored
  - it should be colored by fst, since the win set is monchrome for fst
  - the other pair elem shouldn't be colored, by minimality
  - on the next turn, snd - playning the airing strat, will color the other pair
  - this contradictics the assumption that all points of the win set are colored by fst

This is gonna ake ages
-/



theorem Pairing_Strategy [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)} (hg : Pairing_condition win_sets pairing) :
  (Positional_Game_World win_sets).is_draw_at_worst_snd :=
  by
  use Pairing_sStrat win_sets pairing
  intro f_strat
  sorry

#check Game_wDraw.draw
