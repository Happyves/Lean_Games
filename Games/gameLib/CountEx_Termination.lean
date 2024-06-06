/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.List
import Games.gameLib.Termination
import Mathlib.Tactic



def G : Game_World_wDraw (List ℕ) ℕ where
  init_game_state := []
  fst_win_states := (fun l => if h : l ≠ [] then l.minimum! h = 1 else False)
  snd_win_states := (fun l => if h : l ≠ [] then l.minimum! h = 1 else False)
  draw_states := (fun _ => False)
  fst_transition := fun _ h a => a :: h
  snd_transition := fun _ h a => a :: h
  fst_legal := fun _ hist act => if h : hist ≠ [] then act = (hist.minimum! h) - 1 else act > 0
  snd_legal := fun _ hist act => if h : hist ≠ [] then act = (hist.minimum! h) - 1 else act > 0

lemma G_state_1 (f_strat s_strat : Strategy (List ℕ) ℕ):  ∀ t ≠ 0, G.state_on_turn f_strat s_strat t ≠ [] :=
      by
      intro t tnz con
      dsimp [Game_World_wDraw.state_on_turn] at con
      split at con
      · contradiction
      · dsimp [G] at con
        split at con
        · exact con
        · exact con

lemma G_state_2 (f_strat s_strat : Strategy (List ℕ) ℕ)
  (f_leg : Strategy_legal_fst G.init_game_state G.fst_legal f_strat s_strat)
  (s_leg : Strategy_legal_snd G.init_game_state G.fst_legal f_strat s_strat) :
    let f_act := f_strat [] [] ;
    ∀ t, (ht : t ≠ 0) → (G.state_on_turn f_strat s_strat t).minimum! (G_state_1 f_strat s_strat t ht) = f_act - (t-1) :=
    by
    intro f_act
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




example : G.isWLD ∧ (∀ T : ℕ, ¬ G.isWLD_wBound T) :=
  by
  constructor
  · intro f_strat s_strat f_leg s_leg
    set f_act := f_strat [] [] with f_act_def
    use f_act
    have that := G_state_2 f_strat s_strat f_leg s_leg
    by_cases K : f_act = 0
    · apply Game_World_wDraw.Turn_isWLD.d
      dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G]
      specialize f_leg 0 (by decide)
      dsimp [G, History_on_turn] at f_leg
      rw [dif_neg (by decide)] at f_leg
      rw [← f_act_def, K] at f_leg
      contradiction
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
                 rw [← f_act_def, Nat.add_sub_cancel_left] at that
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
                 rw [← f_act_def, Nat.add_sub_cancel_left] at that
                 exact that
  · intro T
    dsimp [Game_World_wDraw.isWLD_wBound]
    push_neg
    use (fun _ hist => if h : hist ≠ [] then (hist.minimum! h) - 1 else (T+1))
    use (fun _ hist => if h : hist ≠ [] then (hist.minimum! h) - 1 else (T+1))
    have l1 : (Strategy_legal_fst G.init_game_state G.fst_legal (fun x hist => if h : hist ≠ [] then List.minimum! hist h - 1 else T + 1) fun x hist =>if h : hist ≠ [] then List.minimum! hist h - 1 else T + 1) :=
      by
      dsimp [G]
      intro t tf
      cases' t with t
      · dsimp [History_on_turn]
        rw [dif_neg (by decide), dif_neg (by decide)]
        exact Nat.add_pos_right T Nat.le.refl
      · rw [dif_pos (by apply History_on_turn_nonempty_of_succ)]
        dsimp
        rw [dif_pos (by apply History_on_turn_nonempty_of_succ)]
    have l2 : (Strategy_legal_snd G.init_game_state G.fst_legal (fun x hist => if h : hist ≠ [] then List.minimum! hist h - 1 else T + 1) fun x hist =>if h : hist ≠ [] then List.minimum! hist h - 1 else T + 1) :=
      by
      dsimp [G]
      intro t tf
      cases' t with t
      · dsimp [History_on_turn]
        rw [dif_neg (by decide), dif_neg (by decide)]
        exact Nat.add_pos_right T Nat.le.refl
      · rw [dif_pos (by apply History_on_turn_nonempty_of_succ)]
        dsimp
        rw [dif_pos (by apply History_on_turn_nonempty_of_succ)]
    have := G_state_2 (fun x hist => if h : hist ≠ [] then List.minimum! hist h - 1 else T + 1) (fun x hist => if h : hist ≠ [] then List.minimum! hist h - 1 else T + 1) l1 l2
    dsimp at this
    rw [dif_neg (by decide)] at this
    constructor
    · apply l1
    · constructor
      · apply l2
      · intro t tbd con
        by_cases q : t = 0
        · rw [q] at con
          cases' con with tf wf ts ws d
          · dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at wf
            rw [dif_neg (by decide)] at wf
            exact wf
          · dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at ws
            rw [dif_neg (by decide)] at ws
            exact ws
          · dsimp [Game_World_wDraw.state_on_turn, Game_World_wDraw.history_on_turn, History_on_turn, G] at d
        · specialize this t q
          have that : 2 ≤ (List.minimum! (Game_World_wDraw.state_on_turn G (fun x hist => if h : ¬hist = [] then List.minimum! hist h - 1 else T + 1) (fun x hist => if h : ¬hist = [] then List.minimum! hist h - 1 else T + 1) t) ( G_state_1 (fun x hist => if h : ¬hist = [] then List.minimum! hist h - 1 else T + 1) (fun x hist => if h : ¬hist = [] then List.minimum! hist h - 1 else T + 1) t q)) :=
            by
            rw [this]
            rw [← ne_eq, Nat.ne_zero_iff_zero_lt, Nat.lt_iff_add_one_le] at q
            rw [tsub_tsub_assoc (by apply le_trans tbd ; apply Nat.le_succ) q]
            rw [show T+1 = 1+T from by apply add_comm]
            rw [add_comm, Nat.add_sub_assoc tbd, ← add_assoc]
            norm_num
          cases' con with tf wf ts ws d
          · dsimp [G] at wf
            have why := G_state_1 (fun _ hist => if h : hist ≠ [] then (hist.minimum! h) - 1 else (T+1)) (fun _ hist => if h : hist ≠ [] then (hist.minimum! h) - 1 else (T+1)) t q
            dsimp [G] at why
            rw [dif_pos why] at wf
            dsimp [G] at that
            rw [wf] at that
            norm_num at that
          · dsimp [G] at ws
            have why := G_state_1 (fun _ hist => if h : hist ≠ [] then (hist.minimum! h) - 1 else (T+1)) (fun _ hist => if h : hist ≠ [] then (hist.minimum! h) - 1 else (T+1)) t q
            dsimp [G] at why
            rw [dif_pos why] at ws
            dsimp [G] at that
            rw [ws] at that
            norm_num at that
          · dsimp [G] at d
