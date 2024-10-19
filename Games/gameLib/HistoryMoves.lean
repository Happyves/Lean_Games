/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.HistoryAPI
import Games.gameLib.Playability
import Games.gameLib.Termination

def Hist_from_moves (moves : ℕ → β) : ℕ → List β := fun t => ((List.range t).reverse.map moves)

lemma Hist_from_moves_length (moves : ℕ → β) : ∀ t, (Hist_from_moves moves t).length = t := by
  intro t ; dsimp [Hist_from_moves] ; rw [List.length_map, List.length_reverse, List.length_range]

lemma Hist_from_moves_zero (moves : ℕ → β) : (Hist_from_moves moves 0) = [] := by
  rw [← List.length_eq_zero] ; apply Hist_from_moves_length


lemma Hist_from_moves_succ (moves : ℕ → β) : ∀ t, (Hist_from_moves moves (t+1)) = (moves (t)) :: (Hist_from_moves moves (t)):= by
  intro t ; dsimp [Hist_from_moves] ; rw [List.range_succ, List.reverse_append, List.map_append, List.reverse_singleton, List.map_singleton, List.singleton_append]

def Game_World.moves_from_strats (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) :
  ℕ → β :=
  fun t =>
    let H := (g.hist_on_turn f_strat s_strat t)
    if T : Turn_fst (t+1) then (f_strat H.val (by rw [H.property.2] ; exact T) H.property.1).val else (s_strat H.val (by rw [Turn_snd_iff_not_fst, H.property.2] ; exact T) H.property.1).val


lemma Game_World.moves_from_strats_history (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) :
  ∀ t, (g.hist_on_turn f_strat s_strat t).val = Hist_from_moves (moves_from_strats g f_strat s_strat) t :=
  by
  intro t
  induction' t with t ih
  · rfl
  · by_cases T : Turn_fst (t)
    · rw [g.hist_on_turn_fst_to_snd _ _ t T, Hist_from_moves_succ]
      unfold moves_from_strats
      rw [Turn_fst_not_step] at T
      rw [dif_neg T]
      congr
    · rw [g.hist_on_turn_snd_to_fst  _ _ t T, Hist_from_moves_succ]
      unfold moves_from_strats
      rw [Turn_fst_not_step, not_not] at T
      rw [dif_pos T]
      congr


lemma Game_World.moves_from_strats_legal (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) :
  ∀ t, (Turn_fst (t+1) → g.fst_legal (Hist_from_moves (moves_from_strats g f_strat s_strat) t) ((moves_from_strats g f_strat s_strat) t))
    ∧ ( Turn_snd (t+1) → g.snd_legal (Hist_from_moves (moves_from_strats g f_strat s_strat) t) ((moves_from_strats g f_strat s_strat) t)) :=
    by
    intro t
    constructor
    · intro T
      rw [← moves_from_strats_history g f_strat s_strat t]
      unfold moves_from_strats
      rw [dif_pos T]
      apply (f_strat ↑(g.hist_on_turn f_strat s_strat t) _ _).property
    · intro T
      rw [← moves_from_strats_history g f_strat s_strat t]
      unfold moves_from_strats
      rw [dif_neg (by rw [Turn_not_fst_iff_snd] ; exact T)]
      apply (s_strat ↑(g.hist_on_turn f_strat s_strat t) _ _).property

lemma Game_World.moves_from_strats_Hist_legal (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (f_strat : g.fStrategy) (s_strat : g.sStrategy) :
  ∀ t, g.hist_legal (Hist_from_moves (moves_from_strats g f_strat s_strat) t) :=
  by
  intro t
  induction' t with t ih
  · rw [Hist_from_moves_zero]
    apply Game_World.hist_legal.nil
  · rw [Hist_from_moves_succ]
    apply Game_World.hist_legal.cons _ _ _ ih
    rw [Hist_from_moves_length]
    split_ifs with T
    · apply (moves_from_strats_legal g f_strat s_strat t).1 T
    · apply (moves_from_strats_legal g f_strat s_strat t).2 T

noncomputable
def Game_World.fStrategy_from_moves [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, g.hist_legal (Hist_from_moves moves t)) :
  g.fStrategy :=
  fun hist T leg => if M : hist = (Hist_from_moves moves (hist.length))
                    then ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [← M, if_pos T] at now
                      exact now
                      ⟩
                    else (g.exStrat_fst hg hist T leg)


def Game_World.cfStrategy_from_moves [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.cPlayable_fst) (moves : ℕ → β) (hm : ∀ t, g.hist_legal (Hist_from_moves moves t)) :
  g.fStrategy :=
  fun hist T leg => if M : hist = (Hist_from_moves moves (hist.length))
                    then ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [← M, if_pos T] at now
                      exact now
                      ⟩
                    else (hg hist leg T)


noncomputable
def Game_World.sStrategy_from_moves [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, g.hist_legal (Hist_from_moves moves t)) :
  g.sStrategy :=
  fun hist T leg => if M : hist = (Hist_from_moves moves (hist.length))
                    then ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [Turn_snd_iff_not_fst] at T
                      rw [← M, if_neg T] at now
                      exact now
                      ⟩
                    else (g.exStrat_snd hg hist T leg)


def Game_World.csStrategy_from_moves [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.cPlayable_snd) (moves : ℕ → β) (hm : ∀ t, g.hist_legal (Hist_from_moves moves t)) :
  g.sStrategy :=
  fun hist T leg => if M : hist = (Hist_from_moves moves (hist.length))
                    then ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [Turn_snd_iff_not_fst] at T
                      rw [← M, if_neg T] at now
                      exact now
                      ⟩
                    else (hg hist leg T)


lemma Game_World.sStrategy_from_moves_eq  [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, g.hist_legal (Hist_from_moves moves t))
  (hist : List β) (T : Turn_snd (List.length hist + 1)) (leg : g.hist_legal hist) (M : hist = (Hist_from_moves moves (hist.length))) :
  g.sStrategy_from_moves hg moves hm hist T leg = ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [Turn_snd_iff_not_fst] at T
                      rw [← M, if_neg T] at now
                      exact now
                      ⟩ :=
  by
  unfold Game_World.sStrategy_from_moves
  rw [dif_pos M]


lemma Game_World.fStrategy_from_moves_eq  [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, g.hist_legal (Hist_from_moves moves t))
  (hist : List β) (T : Turn_fst (List.length hist + 1)) (leg : g.hist_legal hist) (M : hist = (Hist_from_moves moves (hist.length))) :
  g.fStrategy_from_moves hg moves hm hist T leg = ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [← M, if_pos T] at now
                      exact now
                      ⟩ :=
  by
  unfold Game_World.fStrategy_from_moves
  rw [dif_pos M]

lemma Hist_moves_strats [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hg : g.playable) (moves : ℕ → β) (leg : ∀ t, g.hist_legal (Hist_from_moves moves t)) (t : Nat) :
  Hist_from_moves moves t = (g.hist_on_turn (g.fStrategy_from_moves hg moves leg) (g.sStrategy_from_moves hg moves leg) t).val :=
  by
  induction' t with t ih
  · rw [Hist_from_moves_zero]
    dsimp!
  · rw [Hist_from_moves_succ]
    by_cases q : Turn_fst (t)
    · rw [g.hist_on_turn_fst_to_snd (g.fStrategy_from_moves hg moves leg) (g.sStrategy_from_moves hg moves leg) t q]
      rw [ih]
      congr
      rw [g.sStrategy_from_moves_eq]
      · dsimp!
        rw [g.hist_on_turn_length]
      · rw [g.hist_on_turn_length]
        exact ih.symm
    · rw [Turn_not_fst_iff_snd] at q
      rw [g.hist_on_turn_snd_to_fst (g.fStrategy_from_moves hg moves leg) (g.sStrategy_from_moves hg moves leg) t q]
      rw [ih]
      congr
      rw [g.fStrategy_from_moves_eq]
      · dsimp!
        rw [g.hist_on_turn_length]
      · rw [g.hist_on_turn_length]
        exact ih.symm

def Game_World.isWL_alt (g : Game_World α β) : Prop :=
  ∀ moves : ℕ → β, (∀ t, g.hist_legal (Hist_from_moves moves t)) →
    ∃ T, (g.fst_win_states (Hist_from_moves moves T)) ∨ (g.snd_win_states (Hist_from_moves moves T))



lemma Game_World.isWL_iff_isWL_alt [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] (hg : g.playable) :
  g.isWL ↔ g.isWL_alt :=
  by
  constructor
  · intro h moves leg
    specialize h (fStrategy_from_moves g hg moves leg) (sStrategy_from_moves g hg moves leg)
    obtain ⟨ T,Tp⟩ := h
    use T
    cases' Tp with TF TS
    · left
      convert TF
      apply Hist_moves_strats
    · right
      convert TS
      apply Hist_moves_strats
  · intro h f_strat s_strat
    specialize h (moves_from_strats g f_strat s_strat) (moves_from_strats_Hist_legal g f_strat s_strat)
    obtain ⟨T,q⟩ := h
    use T
    cases' q with F S
    · apply Turn_isWL.wf
      rw [← moves_from_strats_history g f_strat s_strat] at F
      exact F
    · apply Turn_isWL.ws
      rw [← moves_from_strats_history g f_strat s_strat] at S
      exact S
