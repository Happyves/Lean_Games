/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.List
import Games.gameLib.Termination
import Mathlib.Tactic


-- use 1-dim version for ease of expo

def G : Game_World_wDraw (List ℕ) ℕ where
  init_game_state := []
  fst_win_states := (fun l => if h : l ≠ [] then l.minimum! h = 1 else False)
  snd_win_states := (fun l => if h : l ≠ [] then l.minimum! h = 1 else False)
  draw_states := (fun x => x = [])
  fst_transition := fun _ h a => a :: h
  snd_transition := fun _ h a => a :: h
  fst_legal := fun _ hist act => if h : hist ≠ [] then act = (hist.minimum! h) - 1 else True
  snd_legal := fun _ hist act => if h : hist ≠ [] then act = (hist.minimum! h) - 1 else True


example : G.isWLD ∧ (∀ T : ℕ, ¬ G.isWLD_wBound T) :=
  by
  constructor
  · intro f_strat s_strat f_leg s_leg
    set f_act := f_strat [] [] with f_act_def
    use f_act
    have : ∀ t ≠ 0, G.state_on_turn f_strat s_strat t ≠ [] :=
      by
      intro t tnz con
      dsimp [Game_World_wDraw.state_on_turn] at con
      split at con
      · contradiction
      · dsimp [G] at con
        split at con
        · exact con
        · exact con
    have that : ∀ t, (ht : t ≠ 0) → (G.state_on_turn f_strat s_strat t).minimum! (this t ht) = f_act - (t-1) :=
      by
      intro t tnz
      induction' t with t ih
      · contradiction
      · cases' t with t
        · dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G]
          simp_rw [if_pos (show Turn_fst (0+1) from (by decide))]
          dsimp [List.minimum!]
          rfl
        · specialize ih (by exact Nat.succ_ne_zero t)
          unfold Game_World_wDraw.state_on_turn
          dsimp
          split
          · rename_i tf
            dsimp [G, Game_World_wDraw.history_on_turn, History_on_turn, List.minimum!]
            specialize f_leg (t+1) tf
            dsimp [G, History_on_turn] at f_leg
            rw [iff_not_comm.mp (Turn_fst_not_step (t+1))] at tf
            simp_rw [if_neg tf] at *
            rw [dif_pos (by decide)] at f_leg
            simp_rw [f_leg]
            dsimp [List.minimum!]
            -- split and split_ifs fail
            by_cases K : List.minimum! (s_strat [] (History_on_turn [] f_strat s_strat t) :: History_on_turn [] f_strat s_strat t) (_ : ¬s_strat [] (History_on_turn [] f_strat s_strat t) :: History_on_turn [] f_strat s_strat t = []) > 0
            · rw [if_pos (Nat.sub_one_lt_of_le K (by apply le_refl))]
              dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at ih
              simp_rw [if_neg tf] at ih
              rw [ih]
              rfl
            · push_neg at K
              dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at ih
              simp_rw [if_neg tf] at ih
              replace K := Nat.eq_zero_of_le_zero K
              rw [K]
              rw [if_neg (by apply Nat.not_lt_zero)]
              rw [ih] at K
              rw [Nat.succ_sub_one] at *
              rw [Nat.sub_add_eq, K]
          · rename_i tf
            dsimp [G, Game_World_wDraw.history_on_turn, History_on_turn, List.minimum!]
            specialize s_leg (t+1) tf
            dsimp [G, History_on_turn] at s_leg
            rw [iff_not_comm.mp (Turn_fst_not_step (t+1)), not_not] at tf
            simp_rw [if_pos tf] at *
            rw [dif_pos (by decide)] at s_leg
            simp_rw [s_leg]
            dsimp [List.minimum!]
            -- split and split_ifs fail
            by_cases K : List.minimum! (f_strat [] (History_on_turn [] f_strat s_strat t) :: History_on_turn [] f_strat s_strat t) (_ : ¬f_strat [] (History_on_turn [] f_strat s_strat t) :: History_on_turn [] f_strat s_strat t = []) > 0
            · rw [if_pos (Nat.sub_one_lt_of_le K (by apply le_refl))]
              dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at ih
              simp_rw [if_pos tf] at ih
              rw [ih]
              rfl
            · push_neg at K
              dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at ih
              simp_rw [if_pos tf] at ih
              replace K := Nat.eq_zero_of_le_zero K
              rw [K]
              rw [if_neg (by apply Nat.not_lt_zero)]
              rw [ih] at K
              rw [Nat.succ_sub_one] at *
              rw [Nat.sub_add_eq, K]

    by_cases K : f_act = 0
    · apply Game_World_wDraw.Turn_isWLD.d
      dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G]
      rw [← f_act_def, K]
    · by_cases q : Turn_fst f_act
      · apply Game_World_wDraw.Turn_isWLD.wf q
        dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G]
        rw [← f_act_def]
        match fz : f_act with
        | 0 => contradiction
        | n+1 => dsimp
                 rw [if_pos q, dif_pos (by apply List.cons_ne_nil)]
                 specialize that (n+1) (by apply Nat.succ_ne_zero)
                 norm_num at that
                 dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at that
                 simp_rw [if_pos q] at that
                 exact that
      · apply Game_World_wDraw.Turn_isWLD.ws q
        dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G]
        rw [← f_act_def]
        match fz : f_act with
        | 0 => contradiction
        | n+1 => dsimp
                 rw [if_neg q, dif_pos (by apply List.cons_ne_nil)]
                 specialize that (n+1) (by apply Nat.succ_ne_zero)
                 norm_num at that
                 dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at that
                 simp_rw [if_neg q] at that
                 exact that
  · sorry -- refactor hard before getting to this !
