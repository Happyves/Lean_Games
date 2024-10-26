/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Games.exLib.List



lemma Game_World.hist_on_turn_length (g : Game_World α β)
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} : (g.hist_on_turn fst_strat snd_strat t).val.length = t :=
  (g.hist_on_turn fst_strat snd_strat t).prop.2

lemma Symm_Game_World.hist_on_turn_length (g : Symm_Game_World α β)
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} : (g.hist_on_turn fst_strat snd_strat t).val.length = t :=
  (g.hist_on_turn fst_strat snd_strat t).prop.2


lemma Game_World.hist_on_turn_legal (g : Game_World α β)
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} : g.hist_legal (g.hist_on_turn fst_strat snd_strat t).val :=
  (g.hist_on_turn fst_strat snd_strat t).prop.1


lemma Symm_Game_World.hist_on_turn_legal (g : Symm_Game_World α β)
  {fst_strat : g.fStrategy} {snd_strat : g.sStrategy}
  {t : ℕ} : g.hist_legal (g.hist_on_turn fst_strat snd_strat t).val :=
  (g.hist_on_turn fst_strat snd_strat t).prop.1


lemma Game_World.hist_on_turn_of_irrelevant_step (g : Game_World α β)
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (t : ℕ) (motive : List β → Sort _) (ind : motive (g.hist_on_turn fst_strat snd_strat t).val)
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
  (fst_strat : g.fStrategy ) (snd_strat : g.sStrategy)
  (motive : (t : ℕ) → {hist : List β // g.hist_legal hist ∧ hist.length = t} → Sort _)
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


lemma Game_World.fStrat_eq_of_hist_eq (g : Game_World α β) (fs : g.fStrategy)
  (h H : List β) (hh : g.hist_legal h) (hH : g.hist_legal H) (Th : Turn_fst (h.length + 1)) (TH : Turn_fst (H.length + 1))
  (main : h = H) : (fs h Th hh ).val = (fs H TH hH).val :=
  by
  congr
  · rw [main]
  · apply heq_prop
  · apply heq_prop


lemma Game_World.sStrat_eq_of_hist_eq (g : Game_World α β) (fs : g.sStrategy)
  (h H : List β) (hh : g.hist_legal h) (hH : g.hist_legal H) (Th : Turn_snd (h.length + 1)) (TH : Turn_snd (H.length + 1))
  (main : h = H) : (fs h Th hh ).val = (fs H TH hH).val :=
  by
  congr
  · rw [main]
  · apply heq_prop
  · apply heq_prop

lemma Game_World.fStrat_eq_of_strat_hist_eq (g : Game_World α β) (fs fs' : g.fStrategy)
  (h H : List β) (hh : g.hist_legal h) (hH : g.hist_legal H) (Th : Turn_fst (h.length + 1)) (TH : Turn_fst (H.length + 1))
  (main' : fs = fs') (main : h = H) : (fs h Th hh ).val = (fs' H TH hH).val :=
  by
  have : (fs h Th hh ).val = (fs h Th hh ).val := rfl
  convert this
  · exact main.symm
  · exact main'.symm
  · exact main.symm



lemma Game_World.sStrat_eq_of_strat_hist_eq (g : Game_World α β) (fs fs' : g.sStrategy)
  (h H : List β) (hh : g.hist_legal h) (hH : g.hist_legal H) (Th : Turn_snd (h.length + 1)) (TH : Turn_snd (H.length + 1))
  (main' : fs = fs') (main : h = H) : (fs h Th hh ).val = (fs' H TH hH).val :=
  by
  have : (fs h Th hh ).val = (fs h Th hh ).val := rfl
  convert this
  · exact main.symm
  · exact main'.symm
  · exact main.symm

lemma Game_World.hist_on_turn_suffix
  (g : Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy)
  (n m : ℕ) (hmn : m ≤ n) :
  (g.hist_on_turn f_strat s_strat m).val <:+ (g.hist_on_turn f_strat s_strat n).val :=
  by
  induction' n with n ih
  · rw [Nat.le_zero] at hmn
    rw [hmn]
    dsimp!
    exact List.nil_suffix []
  · rw [Nat.le_iff_lt_or_eq] at hmn
    cases' hmn with hmn hmn
    · rw [Nat.lt_succ] at hmn
      apply List.IsSuffix.trans (ih hmn)
      nth_rewrite 1 [hist_on_turn]
      split_ifs with T
      · simp_rw [dif_pos T]
        apply List.suffix_cons
      · simp_rw [dif_neg T]
        apply List.suffix_cons
    · rw [hmn]
      apply List.suffix_rfl

lemma Symm_Game_World.hist_on_turn_suffix
  (g : Symm_Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy)
  (n m : ℕ) (hmn : m ≤ n) :
  (g.hist_on_turn f_strat s_strat m).val <:+ (g.hist_on_turn f_strat s_strat n).val :=
  by
  induction' n with n ih
  · rw [Nat.le_zero] at hmn
    rw [hmn]
    dsimp!
    exact List.nil_suffix []
  · rw [Nat.le_iff_lt_or_eq] at hmn
    cases' hmn with hmn hmn
    · rw [Nat.lt_succ] at hmn
      apply List.IsSuffix.trans (ih hmn)
      dsimp [hist_on_turn, Game_World.hist_on_turn]
      split_ifs with T
      · --simp_rw [dif_pos T]
        apply List.suffix_cons
      · --simp_rw [dif_neg T]
        apply List.suffix_cons
    · rw [hmn]
      apply List.suffix_rfl


lemma Game_World.hist_on_turn_fst_to_snd (g : Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy) (turn : ℕ):
  let H := g.hist_on_turn f_strat s_strat ;
  (T : Turn_fst turn) → (H (turn + 1)).val = (s_strat (H turn).val (by rw [(H turn).property.2, ← Turn_fst_snd_step] ; exact T)  (H turn).property.1).val :: (H turn).val :=
  by
  intro H tf
  dsimp [H, hist_on_turn]
  rw [dif_neg ((Turn_fst_not_step turn).mp tf)]


lemma Game_World.hist_on_turn_snd_to_fst (g : Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy) (turn : ℕ) :
  let H := g.hist_on_turn f_strat s_strat ;
  (T : Turn_snd turn) → (H (turn + 1)).val = (f_strat (H turn).val (by rw [(H turn).property.2, ← Turn_snd_fst_step] ; exact T)  (H turn).property.1).val :: (H turn).val :=
  by
  intro H tf
  dsimp [H, hist_on_turn]
  rw [dif_pos ((Turn_snd_fst_step turn).mp tf)]


lemma Symm_Game_World.hist_on_turn_snd_to_fst (g : Symm_Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy) (turn : ℕ) :
  let H := g.hist_on_turn f_strat s_strat ;
  (T : Turn_snd turn) → (H (turn + 1)).val = (f_strat (H turn).val (by rw [(H turn).property.2, ← Turn_snd_fst_step] ; exact T)  (H turn).property.1).val :: (H turn).val :=
  by
  intro H tf
  dsimp [H, hist_on_turn, Game_World.hist_on_turn]
  rw [dif_pos ((Turn_snd_fst_step turn).mp tf)]


lemma Game_World.hist_on_turn_2step_snd (g : Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy)
  {t : ℕ} (T : Turn_snd t) :
  g.hist_on_turn f_strat s_strat (t+2) =
  (s_strat (g.hist_on_turn f_strat s_strat (t+1)).val (by rw [hist_on_turn_length, ← Turn_snd_step] ; exact T) (g.hist_on_turn f_strat s_strat (t+1)).prop.1).val
    :: (f_strat (g.hist_on_turn f_strat s_strat t).val (by rw [hist_on_turn_length, ← Turn_snd_fst_step] ; exact T) (g.hist_on_turn f_strat s_strat t).prop.1).val
      :: (g.hist_on_turn f_strat s_strat t) :=
  by
  rw [hist_on_turn]
  rw [dif_neg (by rw [← Turn_fst_step] ; exact T)]
  simp only [List.cons.injEq, true_and]
  rw [hist_on_turn]
  rw [dif_pos (by rw [← Turn_snd_fst_step] ; exact T)]

lemma Symm_Game_World.hist_on_turn_2step_snd (g : Symm_Game_World α β)
  (f_strat : g.fStrategy )  (s_strat : g.sStrategy)
  {t : ℕ} (T : Turn_snd t) :
  g.hist_on_turn f_strat s_strat (t+2) =
  (s_strat (g.hist_on_turn f_strat s_strat (t+1)).val (by rw [hist_on_turn_length, ← Turn_snd_step] ; exact T) (g.hist_on_turn f_strat s_strat (t+1)).prop.1).val
    :: (f_strat (g.hist_on_turn f_strat s_strat t).val (by rw [hist_on_turn_length, ← Turn_snd_fst_step] ; exact T) (g.hist_on_turn f_strat s_strat t).prop.1).val
      :: (g.hist_on_turn f_strat s_strat t) :=
  by
  simp_rw [hist_on_turn, Game_World.hist_on_turn]
  rw [dif_neg (by rw [← Turn_fst_step] ; exact T)]
  dsimp
  simp only [List.cons.injEq, true_and]
  rw [dif_pos (by rw [← Turn_snd_fst_step] ; exact T)]
