/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.HistoryAPI
import Games.gameLib.Playability

-- # Staging


def Game_World.fStrat_staged (g : Game_World α β)
  (f_strat : g.fStrategy) (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∀ t, (ht : t < hist.length) → (T : Turn_fst (t+1)) →
    f_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (g.hist_legal_rtake _ _ leg)
    = ⟨ hist.rget ⟨t,ht⟩ , (g.hist_legal_rtake_fst _ _ T ht leg)⟩


def Game_World.fStrat_wHist (g : Game_World α β) (hist : List β) (leg : g.hist_legal hist) :=
  { f_strat : g.fStrategy // g.fStrat_staged f_strat hist leg}


def Game_World.sStrat_staged (g : Game_World α β)
  (s_strat : g.sStrategy) (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∀ t, (ht : t < hist.length) → (T : Turn_snd (t+1)) →
    s_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (g.hist_legal_rtake _ _ leg)
    = ⟨ hist.rget ⟨t,ht⟩ , (g.hist_legal_rtake_snd _ _ T ht leg)⟩


def Game_World.sStrat_wHist (g : Game_World α β) (hist : List β) (leg : g.hist_legal hist) :=
  { s_strat : g.sStrategy // g.sStrat_staged s_strat hist leg}


def Game_World.is_fst_staged_win  (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∃ ws : g.fStrat_wHist hist leg, ∀ snd_s : g.sStrat_wHist hist leg,
  ({g with fst_strat := ws.val, snd_strat := snd_s.val} : Game α β).fst_win


def Game_World.is_snd_staged_win  (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∃ ws : g.sStrat_wHist hist leg, ∀ fst_s : g.fStrat_wHist hist leg,
  ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win

inductive Game_World.has_staged_WL (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) : Prop where
  | wf (h : g.is_fst_staged_win hist leg)
  | ws (h : g.is_snd_staged_win hist leg)

lemma Game_World.fStrat_staged_empty (g : Game_World α β) (f_strat : g.fStrategy) :
  g.fStrat_staged f_strat [] Game_World.hist_legal.nil := by
  intro _ no
  contradiction

lemma Game_World.sStrat_staged_empty (g : Game_World α β) (s_strat : g.sStrategy) :
  g.sStrat_staged s_strat [] Game_World.hist_legal.nil := by
  intro _ no
  contradiction

lemma Game_World.has_WL_iff_has_staged_WL_empty (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )] :
  g.has_WL ↔ g.has_staged_WL [] Game_World.hist_legal.nil :=
  by
  constructor
  · intro h
    cases' h with h h
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_staged_WL.wf
      use ⟨ws, g.fStrat_staged_empty ws⟩
      intro s_strat
      exact ws_prop s_strat.val
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_staged_WL.ws
      use ⟨ws, g.sStrat_staged_empty ws⟩
      intro s_strat
      exact ws_prop s_strat.val
  · intro h
    cases' h with h h
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_WL.wf
      use ws.val
      intro s_strat
      exact ws_prop ⟨s_strat, g.sStrat_staged_empty s_strat⟩
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_WL.ws
      use ws.val
      intro s_strat
      exact ws_prop ⟨s_strat, g.fStrat_staged_empty s_strat⟩


noncomputable
def Game_World.exStrat_staged_fst [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) : g.fStrat_wHist hist leg :=
   ⟨fun h ht hl =>
      if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      then ⟨hist.rget ⟨h.length, M.2⟩, (by convert g.hist_legal_rtake_fst hist h.length ht M.2 leg ; exact M.1)⟩
      else ⟨Classical.choose ((hg h hl).1 ht), Classical.choose_spec ((hg h hl).1 ht)⟩
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact ⟨rfl, hl'⟩
   )⟩


def Game_World.cExStrat_staged_fst [DecidableEq β] (g : Game_World α β) (hg : g.cPlayable_fst)
  (hist : List β) (leg : g.hist_legal hist) : g.fStrat_wHist hist leg :=
   ⟨fun h ht hl =>
      if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      then ⟨hist.rget ⟨h.length, M.2⟩, (by convert g.hist_legal_rtake_fst hist h.length ht M.2 leg ; exact M.1)⟩
      else hg h hl ht
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact ⟨rfl, hl'⟩
   )⟩


noncomputable
def Game_World.exStrat_staged_snd [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) : g.sStrat_wHist hist leg :=
   ⟨fun h ht hl =>
      if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      then ⟨hist.rget ⟨h.length, M.2⟩, (by convert g.hist_legal_rtake_snd hist h.length ht M.2 leg ; exact M.1)⟩
      else ⟨Classical.choose ((hg h hl).2 ht), Classical.choose_spec ((hg h hl).2 ht)⟩
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact ⟨rfl, hl'⟩
   )⟩


def Game_World.cExStrat_staged_snd [DecidableEq β] (g : Game_World α β) (hg : g.cPlayable_snd)
  (hist : List β) (leg : g.hist_legal hist) : g.sStrat_wHist hist leg :=
   ⟨fun h ht hl =>
      if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      then ⟨hist.rget ⟨h.length, M.2⟩, (by convert g.hist_legal_rtake_snd hist h.length ht M.2 leg ; exact M.1)⟩
      else hg h hl ht
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact ⟨rfl, hl'⟩
   )⟩



private lemma Game_World.fStrat_staged_cons_help (g : Game_World α β)
  {act : β} {hist : List β} (tl : t < List.length hist) :
  ∀ x, fst_legal g (List.rtake hist t) x = fst_legal g (List.rtake (act :: hist) t) x :=
    by intro x ; rw [List.rtake_cons_eq_self] ; exact le_of_lt tl


private lemma Game_World.sStrat_staged_cons_help (g : Game_World α β)
  {act : β} {hist : List β} (tl : t < List.length hist) :
  ∀ x, snd_legal g (List.rtake hist t) x = snd_legal g (List.rtake (act :: hist) t) x :=
    by intro x ; rw [List.rtake_cons_eq_self] ; exact le_of_lt tl




-- no prime
lemma Game_World.fStrat_staged_cons_1 (g : Game_World α β) (f_strat : g.fStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.fst_legal hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : g.fStrat_staged f_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg)) :
  g.fStrat_staged f_strat hist leg := by
  intro t tl tf
  specialize st t (by rw [List.length_cons] ; apply lt_trans tl (Nat.lt_succ_self _)) tf
  convert st using 2
  · funext _ ; apply g.fStrat_staged_cons_help tl
  · rw [List.rtake_cons_eq_self] ; exact le_of_lt tl
  · funext _ ; apply g.fStrat_staged_cons_help tl
  · rw [eq_comm] ; apply @List.rget_cons_eq_self _ hist act ⟨t,tl⟩


-- no prime
lemma Game_World.sStrat_staged_cons_1 (g : Game_World α β) (s_strat : g.sStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.snd_legal hist act) (len : List.length hist = t) (T : Turn_snd (t+1))
  (st : g.sStrat_staged s_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [Turn_snd_iff_not_fst] at T ; rw [len, if_neg T] ; exact al) leg)) :
  g.sStrat_staged s_strat hist leg := by
  intro t tl tf
  specialize st t (by rw [List.length_cons] ; apply lt_trans tl (Nat.lt_succ_self _)) tf
  convert st using 2
  · funext _ ; apply g.sStrat_staged_cons_help tl
  · rw [List.rtake_cons_eq_self] ; exact le_of_lt tl
  · funext _ ; apply g.sStrat_staged_cons_help tl
  · rw [eq_comm] ; apply @List.rget_cons_eq_self _ hist act ⟨t,tl⟩


private lemma refactor_1 {act : β} {hist : List β} (T : Turn_snd (t+1))
  (len : List.length hist = t) (t'l : t' < List.length (act :: hist)) (t'f : Turn_fst (t' + 1)) :
  t' < hist.length := by
  apply lt_of_le_of_ne
  · rw [← Nat.lt_succ]
    rw [List.length_cons] at t'l
    exact t'l
  · intro con
    rw [con, len] at t'f
    contradiction

private lemma refactor_2 {act : β} {hist : List β} (T : Turn_fst (t+1))
  (len : List.length hist = t) (t'l : t' < List.length (act :: hist)) (t'f : Turn_snd (t' + 1)) :
  t' < hist.length := by
  apply lt_of_le_of_ne
  · rw [← Nat.lt_succ]
    rw [List.length_cons] at t'l
    exact t'l
  · intro con
    rw [con, len] at t'f
    contradiction

--#exit

-- one prime
lemma Game_World.fStrat_staged_cons_2 (g : Game_World α β) (f_strat : g.fStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.snd_legal hist act) (len : List.length hist = t) (T : Turn_snd (t+1))
  (st : g.fStrat_staged f_strat hist leg) :
  g.fStrat_staged f_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [Turn_snd_iff_not_fst] at T ; rw [len, if_neg T] ; exact al) leg) := by
  intro t' t'l t'f
  have  t'l' := refactor_1 T len t'l t'f
  specialize st t' t'l' t'f
  convert st using 2
  · funext _ ; rw [eq_comm] ; apply (g.fStrat_staged_cons_help t'l')
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · funext _ ; rw [eq_comm] ; apply g.fStrat_staged_cons_help t'l'
  · apply @List.rget_cons_eq_self _ hist act ⟨t', t'l'⟩

-- one prime
lemma Game_World.sStrat_staged_cons_2 (g : Game_World α β) (s_strat : g.sStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.fst_legal hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : g.sStrat_staged s_strat hist leg) :
  g.sStrat_staged s_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg) := by
  intro t' t'l t'f
  have  t'l' := refactor_2 T len t'l t'f
  specialize st t' t'l' t'f
  convert st using 2
  · funext _ ; rw [eq_comm] ; apply g.sStrat_staged_cons_help t'l'
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · funext _ ; rw [eq_comm] ; apply g.sStrat_staged_cons_help t'l'
  · apply @List.rget_cons_eq_self _ hist act ⟨t', t'l'⟩
