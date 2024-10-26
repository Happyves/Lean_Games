/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Positional


/-
This file is in dire need of cleaning.

The file describes the notion of pairing stratgies for positional games.
If there are pairs of tiles for each winning set, that are all distinct
(wihtin and among pairs), then we can play as follows: if the opponent
colors one of the pair elements on one turn, color the other on the next turn.
This way, no winning set can become monochromatic, hence the game will end in a
draw in the worst case for either player.

The main concepts of the file are:
- `Pairing_condition` is the condition for pairing strategies to exist
- `Pairing_StratCore` is the core pairing strategy, which can be use by
  either the first or the second player.
- `Pairing_Strategy` is the theorem that states that if the pairing strat
  conditionas are satisfied, the game ends in a draw in the worst case
  (currently, only for the second player)

-/



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
  (hist : List α) → (leg : (Positional_Game_World win_sets).hist_legal hist) → α :=
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
  (Positional_Game_World win_sets).fStrategy :=
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
  (Positional_Game_World win_sets).sStrategy  :=
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



lemma Positional_Game_World.fst_colored_suffix [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)}
  (h H : List α) (su : h <:+ H) (leg : (Positional_Game_World win_sets).hist_legal H)
  (x : α) (main : (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition h) x = 1) :
  (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition H) x = 1 :=
  by
  induction' H with X H ih
  · rw [List.suffix_nil] at su
    rw [su] at main
    exact main
  · rw [List.suffix_cons_iff] at su
    cases' su with su su
    · rw [su] at main
      exact main
    · cases' leg
      rename_i sofar _
      specialize ih su sofar
      dsimp [State_from_history, Positional_Game_World]
      rw [ite_self]
      cases' H with Y H
      · exfalso
        dsimp [State_from_history, Positional_Game_World] at ih
        contradiction
      · dsimp [State_from_history, Positional_Game_World] at ih
        rw [ite_self] at ih
        dsimp [PosGame_trans] at *
        split_ifs at ih with mem T
        · rw [if_pos (by apply List.mem_cons_of_mem ; exact mem )]
          rw [List.reverse_cons]
          rw [if_pos (by rw [← List.mem_reverse] at mem ; rw [List.indexOf_append_of_mem mem] ; exact T)]
        · contradiction
        · contradiction

lemma Positional_Game_World.snd_colored_suffix [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)}
  (h H : List α) (su : h <:+ H) (leg : (Positional_Game_World win_sets).hist_legal H)
  (x : α) (main : (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition h) x = 2) :
  (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition H) x = 2 :=
  by
  induction' H with X H ih
  · rw [List.suffix_nil] at su
    rw [su] at main
    exact main
  · rw [List.suffix_cons_iff] at su
    cases' su with su su
    · rw [su] at main
      exact main
    · cases' leg
      rename_i sofar _
      specialize ih su sofar
      dsimp [State_from_history, Positional_Game_World]
      rw [ite_self]
      cases' H with Y H
      · exfalso
        dsimp [State_from_history, Positional_Game_World] at ih
        contradiction
      · dsimp [State_from_history, Positional_Game_World] at ih
        rw [ite_self] at ih
        dsimp [PosGame_trans] at *
        split_ifs at ih with mem T
        · contradiction
        · rw [if_pos (by apply List.mem_cons_of_mem ; exact mem )]
          rw [List.reverse_cons]
          rw [if_neg (by rw [← List.mem_reverse] at mem ; rw [List.indexOf_append_of_mem mem] ; exact T)]
        · contradiction




private def colored [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (pairing : win_sets → (α × α))
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (pair : α × α) :=
  {m : Nat |
    let S := (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) m).val) ;
    S pair.1 ≠ 0 ∨ S pair.2 ≠ 0}

private lemma colored_nonempty [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => (0 : Fin 3)) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
   :
  Set.Nonempty (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
  by
  use (n+1)
  have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
  rw [Finset.mem_filter] at mem_fst
  have := Positional_Game_World.fst_colored_suffix H
            ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
            Hsuf
            ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
            (pairing ⟨W, W_win⟩).1 (mem_fst.2)
  dsimp [colored]
  left
  rw [this]
  decide

private lemma first_colored_turn_neq_zero [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ) :
  WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) ≠ 0 :=
  by
  intro con
  have M_mem := WellFounded.min_mem Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  rw [con] at M_mem
  dsimp [colored] at M_mem
  dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, State_from_history, Positional_Game_World] at M_mem
  rw [or_self] at M_mem
  contradiction




lemma Nat.succ_of_ne_zero {n : Nat} (h : n ≠ 0) : ∃ m, n = m+1 := by
  cases' n with n
  · contradiction
  · use n


lemma List.eq_of_mem_cons_not_mem {l : List α} {x y : α} (h1 : y ∉ l) (h2 : y ∈  x :: l) : y = x := by
  simp_all only [mem_cons, or_false]

private lemma second_uncolored [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 = 0) :=
  by
  intro M Hi M_mem
  by_contra con
  replace con := Positional_Game_World_mem_state' win_sets (pairing ⟨W, W_win⟩).2  _ con
  by_cases Q : M = 0
  · exact (first_colored_turn_neq_zero hg f_strat H Hsuf W W_win W_sub) Q
  · obtain ⟨m,mdef⟩ := Nat.succ_of_ne_zero Q
    rw [mdef] at con
    have : m ∉ (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
      by
      intro con
      apply WellFounded.not_lt_min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) con
      dsimp [M] at mdef
      rw [mdef]
      apply Nat.lt_succ_self
    dsimp [colored] at this
    have that : (pairing ⟨W, W_win⟩).1 ∈ (Hi (M)).val :=
      by
      apply Positional_Game_World_mem_state' win_sets
      exact M_mem
    rw [mdef] at that
    simp_rw [← not_and_or, not_not] at this
    have nm1 : (pairing ⟨W, W_win⟩).1 ∉ (Hi m).val :=
      by
      intro con
      exact (Positional_Game_World_mem_state win_sets _ _ con) this.1
    have nm2 : (pairing ⟨W, W_win⟩).2 ∉ (Hi m).val :=
      by
      intro con
      exact (Positional_Game_World_mem_state win_sets _ _ con) this.2
    by_cases T : Turn_fst (m+1)
    · dsimp [Hi, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that con
      rw [dif_pos T] at that con
      replace nm1 := List.eq_of_mem_cons_not_mem nm1 that
      replace nm2 := List.eq_of_mem_cons_not_mem nm2 con
      apply (hg.has_pairing ⟨W, W_win⟩).dif
      rw [nm1,nm2]
    · dsimp [Hi, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that con
      rw [dif_neg T] at that con
      replace nm1 := List.eq_of_mem_cons_not_mem nm1 that
      replace nm2 := List.eq_of_mem_cons_not_mem nm2 con
      apply (hg.has_pairing ⟨W, W_win⟩).dif
      rw [nm1,nm2]


private lemma first_uncolored [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 = 0) :=
  by
  intro M Hi M_mem
  by_contra con
  replace con := Positional_Game_World_mem_state' win_sets (pairing ⟨W, W_win⟩).1  _ con
  by_cases Q : M = 0
  · exact (first_colored_turn_neq_zero hg f_strat H Hsuf W W_win W_sub) Q
  · obtain ⟨m,mdef⟩ := Nat.succ_of_ne_zero Q
    rw [mdef] at con
    have : m ∉ (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
      by
      intro con
      apply WellFounded.not_lt_min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) con
      dsimp [M] at mdef
      rw [mdef]
      apply Nat.lt_succ_self
    dsimp [colored] at this
    have that : (pairing ⟨W, W_win⟩).2 ∈ (Hi (M)).val :=
      by
      apply Positional_Game_World_mem_state' win_sets
      exact M_mem
    rw [mdef] at that
    simp_rw [← not_and_or, not_not] at this
    have nm1 : (pairing ⟨W, W_win⟩).1 ∉ (Hi m).val :=
      by
      intro con
      exact (Positional_Game_World_mem_state win_sets _ _ con) this.1
    have nm2 : (pairing ⟨W, W_win⟩).2 ∉ (Hi m).val :=
      by
      intro con
      exact (Positional_Game_World_mem_state win_sets _ _ con) this.2
    by_cases T : Turn_fst (m+1)
    · dsimp [Hi, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that con
      rw [dif_pos T] at that con
      replace nm2 := List.eq_of_mem_cons_not_mem nm2 that
      replace nm1 := List.eq_of_mem_cons_not_mem nm1 con
      apply (hg.has_pairing ⟨W, W_win⟩).dif
      rw [nm1,nm2]
    · dsimp [Hi, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that con
      rw [dif_neg T] at that con
      replace nm2 := List.eq_of_mem_cons_not_mem nm2 that
      replace nm1 := List.eq_of_mem_cons_not_mem nm1 con
      apply (hg.has_pairing ⟨W, W_win⟩).dif
      rw [nm1,nm2]



private lemma color_pairing_at_win [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing)
  (H : List α) (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ) :
  State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
    (Positional_Game_World win_sets).toGame_World.fst_transition
    (Positional_Game_World win_sets).toGame_World.snd_transition H (pairing { val := W, property := W_win }).1 =
  1 :=
  by
  have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
  rw [Finset.mem_filter] at mem_fst
  apply mem_fst.2

private lemma first_colored_by_fst [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 = 1) :=
  by
  intro M Hi col
  by_contra con
  have bd := Fin.le_val_last (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state (Positional_Game_World win_sets).toGame_World.fst_transition (Positional_Game_World win_sets).toGame_World.snd_transition (↑(Hi M)) (pairing { val := W, property := W_win }).1)
  rw [Fin.ne_iff_vne] at col
  dsimp at col
  simp_rw [← Nat.one_le_iff_ne_zero, le_iff_eq_or_lt] at col
  cases' col with col col
  · simp_rw [Fin.ne_iff_vne] at con
    apply con col.symm
  · rw [← Nat.succ_le] at col
    replace col := le_antisymm bd col
    -- refactor with colored_nonempty
    have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
    rw [Finset.mem_filter] at mem_fst
    have := Positional_Game_World.fst_colored_suffix H
            ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
            Hsuf
            ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
            (pairing ⟨W, W_win⟩).1 (mem_fst.2)
    -- refactor to death ↓
    have refactor_hard : (n+1) ∈ colored pairing f_strat (pairing ⟨W, W_win⟩) :=
      by
      have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
      rw [Finset.mem_filter] at mem_fst
      have := Positional_Game_World.fst_colored_suffix H
                ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
                Hsuf
                ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
                (pairing ⟨W, W_win⟩).1 (mem_fst.2)
      dsimp [colored]
      left
      rw [this]
      decide
    have M_le := WellFounded.min_le Nat.lt_wfRel.wf refactor_hard (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
    have almost := Game_World.hist_on_turn_suffix (Positional_Game_World win_sets).toGame_World f_strat (Pairing_sStrat win_sets pairing) _ _ M_le
    have the := Positional_Game_World.snd_colored_suffix _ _ almost
        ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
        _ col
    have re := Positional_Game_World.fst_colored_suffix _ _ Hsuf
        ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
        (pairing ⟨W, W_win⟩).1 (color_pairing_at_win hg H W W_win W_sub)
    rw [Game_World_wDraw.hist_on_turn , the] at re
    contradiction





private lemma color_pairing_at_win_2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing)
  (H : List α) (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ) :
  State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
    (Positional_Game_World win_sets).toGame_World.fst_transition
    (Positional_Game_World win_sets).toGame_World.snd_transition H (pairing { val := W, property := W_win }).2 =
  1 :=
  by
  have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_snd
  rw [Finset.mem_filter] at mem_fst
  apply mem_fst.2

private lemma second_colored_by_fst [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 = 1) :=
  by
  intro M Hi col
  by_contra con
  have bd := Fin.le_val_last (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state (Positional_Game_World win_sets).toGame_World.fst_transition (Positional_Game_World win_sets).toGame_World.snd_transition (↑(Hi M)) (pairing { val := W, property := W_win }).2)
  rw [Fin.ne_iff_vne] at col
  dsimp at col
  simp_rw [← Nat.one_le_iff_ne_zero, le_iff_eq_or_lt] at col
  cases' col with col col
  · simp_rw [Fin.ne_iff_vne] at con
    apply con col.symm
  · rw [← Nat.succ_le] at col
    replace col := le_antisymm bd col
    -- refactor with colored_nonempty
    have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
    rw [Finset.mem_filter] at mem_fst
    have := Positional_Game_World.fst_colored_suffix H
            ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
            Hsuf
            ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
            (pairing ⟨W, W_win⟩).1 (mem_fst.2)
    -- refactor to death ↓
    have refactor_hard : (n+1) ∈ colored pairing f_strat (pairing ⟨W, W_win⟩) :=
      by
      have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
      rw [Finset.mem_filter] at mem_fst
      have := Positional_Game_World.fst_colored_suffix H
                ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
                Hsuf
                ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
                (pairing ⟨W, W_win⟩).1 (mem_fst.2)
      dsimp [colored]
      left
      rw [this]
      decide
    have M_le := WellFounded.min_le Nat.lt_wfRel.wf refactor_hard (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
    have almost := Game_World.hist_on_turn_suffix (Positional_Game_World win_sets).toGame_World f_strat (Pairing_sStrat win_sets pairing) _ _ M_le
    have the := Positional_Game_World.snd_colored_suffix _ _ almost
        ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
        _ col
    have re := Positional_Game_World.fst_colored_suffix _ _ Hsuf
        ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
        (pairing ⟨W, W_win⟩).2 (color_pairing_at_win_2 hg H W W_win W_sub)
    rw [Game_World_wDraw.hist_on_turn , the] at re
    contradiction


-- may be used to refactor ↑s
lemma help_1 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (T : Turn_fst (m+1) ) → f_strat (Hi m).val (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; exact T) (Hi m).prop.1 = (pairing ⟨W, W_win⟩).1 :=
  by
  intro M Hi S T
  have : m ∉ (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
      by
      intro con
      apply WellFounded.not_lt_min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) con
      rw [mdef]
      apply Nat.lt_succ_self
  dsimp [colored] at this
  have that : (pairing ⟨W, W_win⟩).1 ∈ (Hi (M)).val :=
    by
    apply Positional_Game_World_mem_state' win_sets
    exact S
  dsimp [M] at that
  rw [mdef] at that
  simp_rw [← not_and_or, not_not] at this
  have nm1 : (pairing ⟨W, W_win⟩).1 ∉ (Hi m).val :=
    by
    intro con
    exact (Positional_Game_World_mem_state win_sets _ _ con) this.1
  dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that
  rw [dif_pos T] at that
  replace nm1 := List.eq_of_mem_cons_not_mem nm1 that
  exact nm1.symm




lemma classical_help_1 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) (W : Finset α) (W_win : W ∈ win_sets) :
  (hxf : ∃ w : win_sets, (pairing ⟨W,W_win⟩).1 = (pairing w).1) → (pairing (Classical.choose hxf)).2 = (pairing ⟨W,W_win⟩).2 :=
  by
  intro hxf
  have : Classical.choose hxf = ⟨W,W_win⟩ :=
    by
    by_contra con
    apply (hg.pairing_dif ( Classical.choose hxf) ⟨W,W_win⟩ con).strait_fst
    apply (Classical.choose_spec hxf).symm
  rw [this]


lemma classical_help_2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) (W : Finset α) (W_win : W ∈ win_sets) :
  (hxf : ∃ w : win_sets, (pairing ⟨W,W_win⟩).2 = (pairing w).2) → (pairing (Classical.choose hxf)).1 = (pairing ⟨W,W_win⟩).1 :=
  by
  intro hxf
  have : Classical.choose hxf = ⟨W,W_win⟩ :=
    by
    by_contra con
    apply (hg.pairing_dif ( Classical.choose hxf) ⟨W,W_win⟩ con).strait_snd
    apply (Classical.choose_spec hxf).symm
  rw [this]


lemma Positional_Game_World.nonzero_colored_suffix [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)}
  (h H : List α) (su : h <:+ H) (leg : (Positional_Game_World win_sets).hist_legal H)
  (x : α) (main : (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition h) x ≠ 0) :
  (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition H) x ≠ 0 :=
  by
  have bd := Fin.le_val_last ((State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition h) x)
  rw [Fin.ne_iff_vne] at *
  dsimp at main
  simp_rw [← Nat.one_le_iff_ne_zero, le_iff_eq_or_lt] at main
  cases' main with main main
  · have := Positional_Game_World.fst_colored_suffix _ _ su leg x (by rw [Fin.eq_iff_veq] ; apply main.symm)
    rw [this]
    decide
  · rw [← Nat.succ_le] at main
    replace main := le_antisymm bd main
    have := Positional_Game_World.snd_colored_suffix _ _ su leg x (main)
    rw [Fin.eq_iff_veq] at main
    dsimp at main
    dsimp
    simp_rw [this]
    decide


private lemma help_2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (pairing ⟨W, W_win⟩).2 ∉
    ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) m).val :=
  by
  intro M Hi hit con
  replace con := Positional_Game_World_mem_state win_sets _ _ con
  replace hit := second_uncolored hg f_strat  H Hsuf W W_win W_sub hit
  rw [mdef] at hit
  have con' := Positional_Game_World.nonzero_colored_suffix
      ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) m).val
      ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (m+1)).val
      (by rw [Game_World_wDraw.hist_on_turn] ;  apply Game_World.hist_on_turn_suffix ; exact Nat.le_add_right m 1)
      ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (m+1)).prop.1
      _ con
  exact con' hit



private lemma help_6 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (pairing ⟨W, W_win⟩).1 ∉
    ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) m).val :=
  by
  intro M Hi hit con
  replace con := Positional_Game_World_mem_state win_sets _ _ con
  replace hit := first_uncolored hg f_strat  H Hsuf W W_win W_sub hit
  rw [mdef] at hit
  have con' := Positional_Game_World.nonzero_colored_suffix
      ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) m).val
      ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (m+1)).val
      (by rw [Game_World_wDraw.hist_on_turn] ;  apply Game_World.hist_on_turn_suffix ; exact Nat.le_add_right m 1)
      ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (m+1)).prop.1
      _ con
  exact con' hit



lemma help_3 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (T : ¬ Turn_fst (m+1) ) → (Pairing_sStrat win_sets pairing) (Hi m).val (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; exact T) (Hi m).prop.1 = (pairing ⟨W, W_win⟩).1 :=
  by
  intro M Hi S T
  have : m ∉ (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
      by
      intro con
      apply WellFounded.not_lt_min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) con
      rw [mdef]
      apply Nat.lt_succ_self
  dsimp [colored] at this
  have that : (pairing ⟨W, W_win⟩).1 ∈ (Hi (M)).val :=
    by
    apply Positional_Game_World_mem_state' win_sets
    exact S
  dsimp [M] at that
  rw [mdef] at that
  simp_rw [← not_and_or, not_not] at this
  have nm1 : (pairing ⟨W, W_win⟩).1 ∉ (Hi m).val :=
    by
    intro con
    exact (Positional_Game_World_mem_state win_sets _ _ con) this.1
  dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that
  rw [dif_neg T] at that
  replace nm1 := List.eq_of_mem_cons_not_mem nm1 that
  exact nm1.symm



lemma help_4 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (T : Turn_fst (m+1) )→ f_strat (Hi m).val (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; exact T) (Hi m).prop.1 = (pairing ⟨W, W_win⟩).2 :=
  by
  intro M Hi S T
  have : m ∉ (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
      by
      intro con
      apply WellFounded.not_lt_min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) con
      rw [mdef]
      apply Nat.lt_succ_self
  dsimp [colored] at this
  have that : (pairing ⟨W, W_win⟩).2 ∈ (Hi (M)).val :=
    by
    apply Positional_Game_World_mem_state' win_sets
    exact S
  dsimp [M] at that
  rw [mdef] at that
  simp_rw [← not_and_or, not_not] at this
  have nm1 : (pairing ⟨W, W_win⟩).2 ∉ (Hi m).val :=
    by
    intro con
    exact (Positional_Game_World_mem_state win_sets _ _ con) this.2
  dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that
  rw [dif_pos T] at that
  replace nm1 := List.eq_of_mem_cons_not_mem nm1 that
  exact nm1.symm


lemma help_5 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (T : ¬ Turn_fst (m+1) ) → (Pairing_sStrat win_sets pairing) (Hi m).val (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; exact T) (Hi m).prop.1 = (pairing ⟨W, W_win⟩).2 :=
  by
  intro M Hi S T
  have : m ∉ (colored pairing f_strat (pairing ⟨W, W_win⟩)) :=
      by
      intro con
      apply WellFounded.not_lt_min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) con
      rw [mdef]
      apply Nat.lt_succ_self
  dsimp [colored] at this
  have that : (pairing ⟨W, W_win⟩).2 ∈ (Hi (M)).val :=
    by
    apply Positional_Game_World_mem_state' win_sets
    exact S
  dsimp [M] at that
  rw [mdef] at that
  simp_rw [← not_and_or, not_not] at this
  have nm1 : (pairing ⟨W, W_win⟩).2 ∉ (Hi m).val :=
    by
    intro con
    exact (Positional_Game_World_mem_state win_sets _ _ con) this.2
  dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at that
  rw [dif_neg T] at that
  replace nm1 := List.eq_of_mem_cons_not_mem nm1 that
  exact nm1.symm



private lemma Pairing_StratCore_reacts_fst [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  Turn_fst (M) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (Pairing_StratCore win_sets pairing (Hi M).val (Hi M).prop.1) = (pairing ⟨W, W_win⟩).2 :=
  by
  intro M Hi T hit
  by_cases Q : M = 0
  · exfalso
    exact (first_colored_turn_neq_zero hg f_strat H Hsuf W W_win W_sub) Q
  · obtain ⟨m,mdef⟩ := Nat.succ_of_ne_zero Q
    rw [mdef]
    rw [mdef] at T
    dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn]
    rw [dif_pos T]
    dsimp [Pairing_StratCore]
    have hxf : ∃ w, f_strat (Hi m).val (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; exact T) (Hi m).prop.1 = (pairing w).1 :=
      by use ⟨W, W_win⟩ ; apply help_1 hg f_strat H Hsuf W W_win W_sub mdef hit T
    rw [dif_pos (by convert hxf)]
    have fixHist := help_1 hg f_strat H Hsuf W W_win W_sub mdef hit T
    dsimp [Game_World_wDraw.hist_on_turn] at fixHist
    rw [if_neg (by simp_rw [fixHist] ; have := classical_help_1 hg W W_win (by rw [ help_1 hg f_strat H Hsuf W W_win W_sub mdef hit T] at hxf ; exact hxf) ; rw [this] ; apply List.not_mem_cons_of_ne_of_not_mem ; rw [ne_comm] ; exact (hg.has_pairing ⟨W,W_win⟩).dif ; apply help_2 hg f_strat H Hsuf W W_win W_sub mdef hit)]
    rw [ help_1 hg f_strat H Hsuf W W_win W_sub mdef hit T] at hxf
    convert classical_help_1 hg W W_win hxf



lemma interesting [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing)
  (main : ∃ w : win_sets, last = (pairing w).2) :
  ¬ (∃ w : win_sets, last = (pairing w).1) :=
  by
  obtain ⟨W,W_win,main⟩ := main
  push_neg
  intro w
  by_cases Q : W = w
  · rw [Q, ne_comm]
    apply (hg.has_pairing w).dif
  · rw [ne_comm]
    apply (hg.pairing_dif w W (by rw [ne_comm]; exact Q)).cross_fst




private lemma Pairing_StratCore_reacts_snd [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  Turn_fst (M) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (Pairing_StratCore win_sets pairing (Hi M).val (Hi M).prop.1) = (pairing ⟨W, W_win⟩).1 :=
  by
  intro M Hi T hit
  by_cases Q : M = 0
  · exfalso
    exact (first_colored_turn_neq_zero hg f_strat H Hsuf W W_win W_sub) Q
  · obtain ⟨m,mdef⟩ := Nat.succ_of_ne_zero Q
    rw [mdef]
    rw [mdef] at T
    dsimp [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn]
    rw [dif_pos T]
    dsimp [Pairing_StratCore]
    have hxf : ∃ w, f_strat (Hi m).val (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; exact T) (Hi m).prop.1 = (pairing w).2 :=
      by use ⟨W, W_win⟩ ; apply help_4 hg f_strat H Hsuf W W_win W_sub mdef hit T
    have fixHist := interesting hg hxf
    have fixHist2 := help_4 hg f_strat H Hsuf W W_win W_sub mdef hit T
    dsimp [Game_World_wDraw.hist_on_turn] at fixHist fixHist2 hxf
    rw [dif_neg fixHist]
    rw [dif_pos hxf]
    rw [if_neg (by simp_rw [fixHist2] ; have := classical_help_2 hg W W_win (by rw [fixHist2] at hxf ; exact hxf) ; rw [this] ; apply List.not_mem_cons_of_ne_of_not_mem ; rw [ne_comm] ; exact ne_comm.mp (hg.has_pairing ⟨W,W_win⟩).dif ; apply help_6 hg f_strat H Hsuf W W_win W_sub mdef hit)]
    rw [fixHist2] at hxf
    convert classical_help_2 hg W W_win hxf



lemma help_1_3 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (Hi (M)).val = (pairing ⟨W, W_win⟩).1  :: (Hi (m)).val :=
  by
  intro M Hi S
  by_cases T : Turn_fst (m+1)
  · dsimp [M]
    rw [mdef, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_pos T]
    dsimp
    congr
    apply help_1 hg f_strat H Hsuf W W_win W_sub mdef S T
  · dsimp [M]
    rw [mdef, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_neg T]
    dsimp
    congr
    apply help_3 hg f_strat H Hsuf W W_win W_sub mdef S T


lemma help_1_3_2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (Hi (M)).val = (pairing ⟨W, W_win⟩).2 :: (Hi (m)).val :=
  by
  intro M Hi S
  by_cases T : Turn_fst (m+1)
  · dsimp [M]
    rw [mdef, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_pos T]
    dsimp
    congr
    apply help_4 hg f_strat H Hsuf W W_win W_sub mdef S T
  · dsimp [M]
    rw [mdef, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_neg T]
    dsimp
    congr
    apply help_5 hg f_strat H Hsuf W W_win W_sub mdef S T


lemma almost [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      ((pairing ⟨W, W_win⟩).1  :: (Hi (m)).val)
      (pairing ⟨W, W_win⟩).1 = 1) :=
  by
  intro M Hi S
  rw [← help_1_3 hg f_strat H Hsuf W W_win W_sub mdef S]
  apply first_colored_by_fst hg f_strat H Hsuf W W_win W_sub S



lemma almost2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      ((pairing ⟨W, W_win⟩).2  :: (Hi (m)).val)
      (pairing ⟨W, W_win⟩).2 = 1) :=
  by
  intro M Hi S
  rw [← help_1_3_2 hg f_strat H Hsuf W W_win W_sub mdef S]
  apply second_colored_by_fst hg f_strat H Hsuf W W_win W_sub S




lemma there [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  Turn_fst M :=
  by
  intro M Hi S
  dsimp [M]
  rw [mdef]
  have := Positional_Game_World.turn_fst_of_col_fst (Hi m).val (pairing ⟨W, W_win⟩).1
    (by have := (Hi M).prop.1 ; rw [help_1_3 hg f_strat H Hsuf W W_win W_sub mdef S] at this ; exact this)
    (almost hg f_strat H Hsuf W W_win W_sub mdef S)
    (by rw [← Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral]
        apply Neu
        rw [← Nat.succ_le_succ_iff, Nat.succ_eq_add_one, ← mdef]
        apply  WellFounded.min_le Nat.lt_wfRel.wf _ (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
        -- refactor
        have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
        rw [Finset.mem_filter] at mem_fst
        have := Positional_Game_World.fst_colored_suffix H
                  ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
                  Hsuf
                  ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
                  (pairing ⟨W, W_win⟩).1 (mem_fst.2)
        dsimp [colored]
        left
        rw [this]
        decide
    )
  simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] at this
  exact this



lemma there2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  Turn_fst M :=
  by
  intro M Hi S
  dsimp [M]
  rw [mdef]
  have := Positional_Game_World.turn_fst_of_col_fst (Hi m).val (pairing ⟨W, W_win⟩).2
    (by have := (Hi M).prop.1 ; rw [help_1_3_2 hg f_strat H Hsuf W W_win W_sub mdef S] at this ; exact this)
    (almost2 hg f_strat H Hsuf W W_win W_sub mdef S)
    (by rw [← Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral]
        apply Neu
        rw [← Nat.succ_le_succ_iff, Nat.succ_eq_add_one, ← mdef]
        apply  WellFounded.min_le Nat.lt_wfRel.wf _ (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
        -- refactor
        have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
        rw [Finset.mem_filter] at mem_fst
        have := Positional_Game_World.fst_colored_suffix H
                  ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
                  Hsuf
                  ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
                  (pairing ⟨W, W_win⟩).1 (mem_fst.2)
        dsimp [colored]
        left
        rw [this]
        decide
    )
  simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] at this
  exact this


lemma Hit_turn_is_neutral [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  State_from_history_neutral_wDraw (Positional_Game_World win_sets).toGame_World.init_game_state
  (Positional_Game_World win_sets).toGame_World.fst_win_states
  (Positional_Game_World win_sets).toGame_World.snd_win_states (Positional_Game_World win_sets).draw_states ↑(Hi M) :=
  by
  intro M Hi
  have : M ≤ n+1 :=
    by
    apply  WellFounded.min_le Nat.lt_wfRel.wf _ (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
    -- refactor
    have mem_fst := W_sub (hg.has_pairing ⟨W, W_win⟩).mem_fst
    rw [Finset.mem_filter] at mem_fst
    have := Positional_Game_World.fst_colored_suffix H
              ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val
              Hsuf
              ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).prop.1
              (pairing ⟨W, W_win⟩).1 (mem_fst.2)
    dsimp [colored]
    left
    rw [this]
    decide
  rw [le_iff_eq_or_lt] at this
  cases' this with that that
  · exfalso
    have fst := W_sub (hg.has_pairing ⟨W,W_win⟩).mem_fst
    have snd := W_sub (hg.has_pairing ⟨W,W_win⟩).mem_snd
    rw [Finset.mem_filter] at fst snd
    have but := second_uncolored hg f_strat H Hsuf W W_win W_sub
      (by intro con
          have one := Positional_Game_World.fst_colored_suffix _ _ Hsuf (Hi (n+1)).prop.1 (pairing ⟨W, W_win⟩).1 fst.2
          rw [← that] at one
          rw [one] at con
          contradiction
       )
    have two := Positional_Game_World.fst_colored_suffix _ _ Hsuf (Hi (n+1)).prop.1 (pairing ⟨W, W_win⟩).2 snd.2
    rw [← that] at two
    rw [two] at but
    contradiction
  · rw [Nat.lt_succ] at that
    rw [← Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral]
    apply Neu
    exact that



lemma Pairing_StratCore_colors_reacts_fst_consequemce [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi (M+1)) (pairing ⟨W, W_win⟩).2 = 2) :=
  by
  intro M Hi S
  have T := there hg f_strat Neu H Hsuf W W_win W_sub mdef S
  dsimp [M]
  simp_rw [Turn_fst_not_step M] at T
  rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_neg T]
  dsimp
  have RW := Pairing_StratCore_reacts_fst hg f_strat H Hsuf W W_win W_sub
        (there hg f_strat Neu H Hsuf W W_win W_sub mdef S) S
  dsimp [Pairing_sStrat]
  dsimp [Game_World_wDraw.hist_on_turn] at RW
  rw [RW]
  apply Positional_Game_World.col_snd_of_turn_snd (Hi M).val (pairing ⟨W, W_win⟩).2
    (by have := (Hi (M+1)).prop.1
        simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_neg T] at this
        dsimp [Pairing_sStrat] at this
        simp_rw [RW] at this
        exact this
    )
    (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; apply T )
    (by apply Hit_turn_is_neutral hg f_strat Neu H Hsuf W W_win W_sub
    )



lemma Pairing_StratCore_colors_reacts_snd_consequemce [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi (M+1)) (pairing ⟨W, W_win⟩).1 = 2) :=
  by
  intro M Hi S
  have T := there2 hg f_strat Neu H Hsuf W W_win W_sub mdef S
  dsimp [M]
  simp_rw [Turn_fst_not_step M] at T
  rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_neg T]
  dsimp
  have RW := Pairing_StratCore_reacts_snd hg f_strat H Hsuf W W_win W_sub
        (there2 hg f_strat Neu H Hsuf W W_win W_sub mdef S) S
  dsimp [Pairing_sStrat]
  dsimp [Game_World_wDraw.hist_on_turn] at RW
  rw [RW]
  apply Positional_Game_World.col_snd_of_turn_snd (Hi M).val (pairing ⟨W, W_win⟩).1
    (by have := (Hi (M+1)).prop.1
        simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, dif_neg T] at this
        dsimp [Pairing_sStrat] at this
        simp_rw [RW] at this
        exact this
    )
    (by simp_rw [Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn_length] ; apply T )
    (by apply Hit_turn_is_neutral hg f_strat Neu H Hsuf W W_win W_sub
    )



lemma Pairing_Strategy_Main_1 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).1 ≠ 0) →
  False :=
  by
  intro M Hi S
  by_cases Q : (n+1) ≤ M+1
  · have su := List.IsSuffix.trans Hsuf (Game_World.hist_on_turn_suffix _ _ _ _ _ Q)
    replace su := Positional_Game_World.fst_colored_suffix _ _ su (Hi (M+1)).prop.1 (pairing ⟨W, W_win⟩).2
      (by have := W_sub (hg.has_pairing ⟨W,W_win⟩).mem_snd ; rw [Finset.mem_filter] at this ; exact this.2)
    have fixHist := Pairing_StratCore_colors_reacts_fst_consequemce hg f_strat Neu H Hsuf W W_win W_sub mdef S
    dsimp [Game_World_wDraw.hist_on_turn] at fixHist
    rw [fixHist] at su
    contradiction
  · have su := (Game_World.hist_on_turn_suffix (Positional_Game_World win_sets).toGame_World f_strat (Pairing_sStrat win_sets pairing) _ _ (le_of_lt (not_le.mp Q)))
    have one := Positional_Game_World.fst_colored_suffix _ _ Hsuf (Hi (n+1)).prop.1 (pairing ⟨W, W_win⟩).2
      (by have := W_sub (hg.has_pairing ⟨W,W_win⟩).mem_snd ; rw [Finset.mem_filter] at this ; exact this.2)
    have two := Positional_Game_World.snd_colored_suffix _ _ su (Hi (n+1)).prop.1 (pairing ⟨W, W_win⟩).2
      (by apply Pairing_StratCore_colors_reacts_fst_consequemce hg f_strat Neu H Hsuf W W_win W_sub mdef S)
    dsimp [Game_World_wDraw.hist_on_turn] at one
    rw [one] at two
    contradiction





lemma Pairing_Strategy_Main_2 [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ)
  {m : Nat} (mdef : WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub) = m+1)
  : let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  let Hi :=  (((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing)))
  (State_from_history (Positional_Game_World win_sets).toGame_World.init_game_state
      (Positional_Game_World win_sets).toGame_World.fst_transition
      (Positional_Game_World win_sets).toGame_World.snd_transition
      (Hi M) (pairing ⟨W, W_win⟩).2 ≠ 0) →
  False :=
  by
  intro M Hi S
  by_cases Q : (n+1) ≤ M+1
  · have su := List.IsSuffix.trans Hsuf (Game_World.hist_on_turn_suffix _ _ _ _ _ Q)
    replace su := Positional_Game_World.fst_colored_suffix _ _ su (Hi (M+1)).prop.1 (pairing ⟨W, W_win⟩).1
      (by have := W_sub (hg.has_pairing ⟨W,W_win⟩).mem_fst ; rw [Finset.mem_filter] at this ; exact this.2)
    have fixHist := Pairing_StratCore_colors_reacts_snd_consequemce hg f_strat Neu H Hsuf W W_win W_sub mdef S
    dsimp [Game_World_wDraw.hist_on_turn] at fixHist
    rw [fixHist] at su
    contradiction
  · have su := (Game_World.hist_on_turn_suffix (Positional_Game_World win_sets).toGame_World f_strat (Pairing_sStrat win_sets pairing) _ _ (le_of_lt (not_le.mp Q)))
    have one := Positional_Game_World.fst_colored_suffix _ _ Hsuf (Hi (n+1)).prop.1 (pairing ⟨W, W_win⟩).1
      (by have := W_sub (hg.has_pairing ⟨W,W_win⟩).mem_fst ; rw [Finset.mem_filter] at this ; exact this.2)
    have two := Positional_Game_World.snd_colored_suffix _ _ su (Hi (n+1)).prop.1 (pairing ⟨W, W_win⟩).1
      (by apply Pairing_StratCore_colors_reacts_snd_consequemce hg f_strat Neu H Hsuf W W_win W_sub mdef S)
    dsimp [Game_World_wDraw.hist_on_turn] at one
    rw [one] at two
    contradiction



theorem Pairing_Strategy_Main [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (hg : Pairing_condition win_sets pairing) {n : Nat}
  (f_strat : (Positional_Game_World win_sets).fStrategy)
  (Neu : ∀ k ≤ n, Game_World_wDraw.state_on_turn_neutral (Positional_Game_World win_sets) f_strat (Pairing_sStrat win_sets pairing) k)
  (H : List α) (Hsuf : H <:+ ((Positional_Game_World win_sets).hist_on_turn f_strat (Pairing_sStrat win_sets pairing) (n+1)).val )
  (W : Finset α) (W_win : W ∈ win_sets) (W_sub : W ⊆ Finset.filter (fun x => State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) H x = 1) Finset.univ) :
  False :=
  by
  let M := WellFounded.min Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
  by_cases Q : M = 0
  · exfalso
    exact (first_colored_turn_neq_zero hg f_strat H Hsuf W W_win W_sub) Q
  · obtain ⟨m,mdef⟩ := Nat.succ_of_ne_zero Q
    have M_mem := WellFounded.min_mem Nat.lt_wfRel.wf (colored pairing f_strat (pairing ⟨W, W_win⟩)) (colored_nonempty hg f_strat H Hsuf W W_win W_sub)
    dsimp [colored] at M_mem
    cases' M_mem with M_mem M_mem
    · apply Pairing_Strategy_Main_1 hg f_strat Neu H Hsuf W W_win W_sub mdef M_mem
    · apply Pairing_Strategy_Main_2 hg f_strat Neu H Hsuf W W_win W_sub mdef M_mem





theorem Pairing_Strategy [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {pairing : win_sets → (α × α)}
  (win_sets_nontrivial : ∅ ∉ win_sets) (hg : Pairing_condition win_sets pairing) :
  (Positional_Game_World win_sets).is_draw_at_worst_snd :=
  by
  use Pairing_sStrat win_sets pairing
  intro f_strat
  obtain ⟨T,Tend,Tpre⟩ := Positional_Game_World.terminates win_sets win_sets_nontrivial f_strat (Pairing_sStrat win_sets pairing)
  rw [Game_World_wDraw.state_on_turn_neutral, not_not] at Tend
  cases' Tend with F S D
  · exfalso
    dsimp [Positional_Game_World] at F
    obtain ⟨H, Hsuf, Hwin⟩ := F
    obtain ⟨W,W_win, W_sub⟩ := Hwin
    apply Pairing_Strategy_Main hg  f_strat Tpre H Hsuf W W_win W_sub
  · left
    use (T+1)
    constructor
    · apply S
    · intro t tlT
      rw [Nat.lt_succ] at tlT
      exact Tpre t tlT
  · right
    use (T+1)
    constructor
    · apply D
    · intro t tlT
      rw [Nat.lt_succ] at tlT
      exact Tpre t tlT
