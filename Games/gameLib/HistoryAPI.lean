/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Games.exLib.List



lemma Game_World.hist_on_turn_length (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} : (g.hist_on_turn fst_strat snd_strat t).val.length = t :=
  (g.hist_on_turn fst_strat snd_strat t).prop.2

lemma Game_World.hist_on_turn_legal (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} : g.hist_legal (g.hist_on_turn fst_strat snd_strat t).val :=
  (g.hist_on_turn fst_strat snd_strat t).prop.1


lemma Game_World.hist_on_turn_of_irrelevant_step (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (motive : List β → Type _) (ind : motive (g.hist_on_turn fst_strat snd_strat t).val)
  (irrel : ∀ act, g.hist_legal (act :: (g.hist_on_turn fst_strat snd_strat t).val) →
      motive (g.hist_on_turn fst_strat snd_strat t).val → motive (act :: (g.hist_on_turn fst_strat snd_strat t).val)) :
  motive (g.hist_on_turn fst_strat snd_strat (t+1)).val :=
  by
  dsimp [hist_on_turn]
  split_ifs with T
  · apply irrel _ _ ind
    have := (g.hist_on_turn fst_strat snd_strat (t+1)).prop.1
    rw [hist_on_turn, dif_pos T] at this
    exact this
  · apply irrel _ _ ind
    have := (g.hist_on_turn fst_strat snd_strat (t+1)).prop.1
    rw [hist_on_turn, dif_neg T] at this
    exact this


lemma Game_World.hist_on_turn_induction (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (motive : (t : ℕ) → {hist : List β // g.hist_legal hist ∧ hist.length = t} → Type _)
  (base : motive 0 (g.hist_on_turn fst_strat snd_strat 0))
  (step_fst : (t : ℕ) → (T : Turn_fst (t+1)) →
      let h := g.hist_on_turn fst_strat snd_strat t
      motive t h →
      let T' : Turn_fst (List.length h.val + 1) := by rw [h.property.2] ; exact T ;
      let act := (fst_strat h.val T' h.property.1).val ;
      let leg := (fst_strat h.val T' h.property.1).property ;
      motive (t+1) ⟨act :: h.val , ⟨Game_World.hist_legal.cons h.val act (by rw [if_pos T'] ; exact leg) h.property.1, (by dsimp ; rw [h.property.2])⟩⟩
      )
  (step_snd : (t : ℕ) → (T : Turn_snd (t+1)) →
      let h := g.hist_on_turn fst_strat snd_strat t
      motive t h →
      let T' : Turn_snd (List.length h.val + 1) := by rw [Turn_snd_iff_not_fst , h.property.2] ; exact T ;
      let act := (snd_strat h.val T' h.property.1).val ;
      let leg := (snd_strat h.val T' h.property.1).property ;
      motive (t+1) ⟨ act :: h.val , ⟨Game_World.hist_legal.cons h.val act (by rw [if_neg ] ; exact leg ; rw [Turn_not_fst_iff_snd] ; exact T') h.property.1, (by dsimp ; rw [h.property.2])⟩⟩
      ) (t : ℕ):
  motive t (g.hist_on_turn fst_strat snd_strat t) :=
  by
  induction' t with t ih
  · exact base
  · by_cases T : Turn_fst (t+1)
    · rw [hist_on_turn, dif_pos T]
      exact step_fst t T ih
    · rw [hist_on_turn, dif_neg T]
      exact step_snd t T ih


lemma Game_World.hist_legal_suffix (g : Game_World α β)
  (pre post : List β) :
  g.hist_legal (post ++ pre) → g.hist_legal pre :=
  by
  intro main
  induction' post with x l ih
  · rw [List.nil_append] at main
    exact main
  · cases' main
    rename_i yes _
    exact ih yes

lemma Game_World.hist_legal_rtake (g : Game_World α β)
  (hist : List β) (t : Nat) :
  g.hist_legal hist → g.hist_legal (hist.rtake t) := by
  intro main
  rw [← hist.rdrop_append_rtake t] at main
  apply g.hist_legal_suffix _ _ main




lemma Game_World.hist_legal_rtake_fst (g : Game_World α β)
  (hist : List β) (t : Nat) (htT : Turn_fst (t+1)) (htL : t < hist.length)
  (main : g.hist_legal hist) : g.fst_legal (hist.rtake t) (hist.rget ⟨t, htL⟩) := by
  replace main := g.hist_legal_rtake _ (t+1) main
  rw [@List.rget_cons_rtake _ _ ⟨t,htL⟩ ] at main
  cases' main
  rename_i _ now
  rw [List.length_rtake (le_of_lt htL), if_pos htT] at now
  exact now

lemma Game_World.hist_legal_rtake_snd (g : Game_World α β)
  (hist : List β) (t : Nat) (htT : Turn_snd (t+1)) (htL : t < hist.length)
  (main : g.hist_legal hist) : g.snd_legal (hist.rtake t) (hist.rget ⟨t, htL⟩) := by
  replace main := g.hist_legal_rtake _ (t+1) main
  rw [@List.rget_cons_rtake _ _ ⟨t,htL⟩ ] at main
  cases' main
  rename_i _ now
  rw [Turn_snd_iff_not_fst] at htT
  rw [List.length_rtake (le_of_lt htL), if_neg htT] at now
  exact now
