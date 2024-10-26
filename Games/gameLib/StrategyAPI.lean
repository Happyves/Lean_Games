/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.HistoryAPI
import Games.gameLib.Playability
import Games.exLib.General




/-
This file collects API about strategies.
Currently, it mostly contains API about staging, which is required for
applying Conway induction in Zermelo.

The main concepts are:
- `fStrat_staged` and `sStrat_staged`, which define staging
- `has_WL_iff_has_staged_WL_empty` is used to link staged winning and actual winning
- `fStrat_winner` and `sStrat_winner` : in game worlds where, given a certain history,
  one player has a staged winning strategy (it wins agains all staged strategies),
  for all possible moves of the other player, `fStrat_winner` and `sStrat_winner` define
  stratgies that will be a staged winning strategy for the initial history, as is shown
  in `fStrat_winner_wins` and `sStrat_winner_wins`.
-/

-- # Staging


/--
In the context of a `Game_World`, we call a strategy "staged" wrt. a legal
history of moves, if the moves played by the strategy on that history are
precisely the moves from the history.
-/
def Game_World.fStrat_staged (g : Game_World α β)
  (f_strat : g.fStrategy) (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∀ t, (ht : t < hist.length) → (T : Turn_fst (t+1)) →
    f_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (g.hist_legal_rtake _ _ leg)
    = ⟨ hist.rget ⟨t,ht⟩ , (g.hist_legal_rtake_fst _ _ T ht leg)⟩


def Game_World.fStrat_wHist (g : Game_World α β) (hist : List β) (leg : g.hist_legal hist) :=
  { f_strat : g.fStrategy // g.fStrat_staged f_strat hist leg}


/--
In the context of a `Game_World`, we call a strategy "staged" wrt. a legal
history of moves, if the moves played by the strategy on that history are
precisely the moves from the history.
-/
def Game_World.sStrat_staged (g : Game_World α β)
  (s_strat : g.sStrategy) (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∀ t, (ht : t < hist.length) → (T : Turn_snd (t+1)) →
    s_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (g.hist_legal_rtake _ _ leg)
    = ⟨ hist.rget ⟨t,ht⟩ , (g.hist_legal_rtake_snd _ _ T ht leg)⟩


def Game_World.sStrat_wHist (g : Game_World α β) (hist : List β) (leg : g.hist_legal hist) :=
  { s_strat : g.sStrategy // g.sStrat_staged s_strat hist leg}


def Game_World.is_fst_staged_win  (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∃ ws : g.fStrat_wHist hist leg, ∀ snd_s : g.sStrat_wHist hist leg,
  ({g with fst_strat := ws.val, snd_strat := snd_s.val} : Game α β).fst_win


def Game_World.is_snd_staged_win  (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal hist) : Prop :=
  ∃ ws : g.sStrat_wHist hist leg, ∀ fst_s : g.fStrat_wHist hist leg,
  ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win

inductive Game_World.has_staged_WL (g : Game_World α β)
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

lemma Game_World.has_WL_iff_has_staged_WL_empty (g : Game_World α β) :
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


-- three primes
lemma Game_World.fStrat_staged_cons_4 (g : Game_World α β) (f_strat : g.fStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.snd_legal hist act) (len : List.length hist = t) (T : Turn_snd (t+1))
  (st : g.fStrat_staged  f_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [Turn_snd_iff_not_fst] at T ; rw [len, if_neg T] ; exact al) leg)) :
  g.fStrat_staged f_strat hist leg := by
  intro t tl tf
  specialize st t (by rw [List.length_cons] ; apply lt_trans tl ; apply Nat.lt_succ_self) tf
  convert st using 2
  · funext _ ; apply g.fStrat_staged_cons_help tl
  · rw [List.rtake_cons_eq_self] ; exact le_of_lt tl
  · funext _ ; apply g.fStrat_staged_cons_help tl
  · rw [eq_comm] ; apply @List.rget_cons_eq_self _ hist act ⟨t,tl⟩



private lemma refactor_3 (t'l : t' < List.length hist) : t' < (act :: hist).length := by
    apply lt_of_le_of_ne
    · rw [← Nat.lt_succ, List.length_cons]
      apply lt_trans t'l
      rw [Nat.lt_succ]
      apply Nat.le_succ
    · intro con
      rw [List.length_cons] at con
      rw [con] at t'l
      exfalso
      apply Nat.not_succ_lt_self t'l

-- two primes
lemma Game_World.fStrat_staged_cons_3 (g : Game_World α β) (f_strat : g.fStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.fst_legal hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : g.fStrat_staged f_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg)) :
  g.fStrat_staged f_strat hist leg := by
  intro t' t'l t'f
  have  t'l' : t' < (act :: hist).length := refactor_3 t'l
  specialize st t' t'l' t'f
  convert st using 2
  · funext _ ; apply g.fStrat_staged_cons_help t'l
  · rw [List.rtake_cons_eq_self] ;exact le_of_lt t'l
  · funext _ ; apply g.fStrat_staged_cons_help t'l
  · rw [eq_comm] ; apply @List.rget_cons_eq_self _ hist act ⟨t', t'l⟩


-- two primes
lemma Game_World.sStrat_staged_cons_3 (g : Game_World α β) (s_strat : g.sStrategy) (act : β) (hist : List β)
  (leg : g.hist_legal hist) (al : g.fst_legal hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : g.sStrat_staged s_strat (act :: hist) (Game_World.hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg)) :
  g.sStrat_staged s_strat hist leg := by
  intro t' t'l t'f
  have  t'l' : t' < (act :: hist).length := refactor_3 t'l
  specialize st t' t'l' t'f
  convert st using 2
  · funext _ ; apply g.sStrat_staged_cons_help t'l
  · rw [List.rtake_cons_eq_self] ;exact le_of_lt t'l
  · funext _ ; apply g.sStrat_staged_cons_help t'l
  · rw [eq_comm] ; apply @List.rget_cons_eq_self _ hist act ⟨t', t'l⟩



lemma Game_World.History_of_staged_length (g : Game_World α β)

  (hist : List β) (leg : g.hist_legal hist)
  (f_strat : g.fStrat_wHist hist leg) (s_strat : g.sStrat_wHist hist leg) :
  (g.hist_on_turn f_strat.val s_strat.val hist.length).val = hist := by
  induction' hist with x l ih
  · rfl
  · cases' leg
    rename_i sofar now
    dsimp [hist_on_turn]
    split_ifs with T
    · rw [if_pos T] at now
      dsimp
      have main : ↑(g.hist_on_turn (f_strat.val) (s_strat.val) (List.length l)) = l := ih sofar ⟨f_strat.val, g.fStrat_staged_cons_3 _ _ _ sofar now rfl T f_strat.prop⟩ ⟨s_strat.val, g.sStrat_staged_cons_3 _ _ _ sofar now rfl T s_strat.prop⟩
      congr
      · have := (f_strat).prop l.length (by dsimp ; apply Nat.lt_succ_self) T
        have that := @List.rtake_cons_eq_self _ l x _ (le_refl l.length)
        rw [List.rtake_length] at that
        replace this := congr_arg Subtype.val this
        convert this
        · rw [that]
          apply main
        · rw [that]
          apply main
        · unfold List.rget
          dsimp!
          simp_rw [Nat.succ_sub_one, Nat.sub_self]
          rfl
    · rw [if_neg T] at now
      rw [← Turn_snd_iff_not_fst] at T
      dsimp
      have main : ↑(g.hist_on_turn (f_strat.val) (s_strat.val) (List.length l)) = l := ih sofar ⟨f_strat.val, g.fStrat_staged_cons_4 _ _ _ sofar now rfl T f_strat.prop⟩ ⟨s_strat.val, g.sStrat_staged_cons_1 _ _ _ sofar now rfl T s_strat.prop⟩
      congr
      · have := (s_strat).prop l.length (by dsimp ; apply Nat.lt_succ_self) T
        have that := @List.rtake_cons_eq_self _ l x _ (le_refl l.length)
        rw [List.rtake_length] at that
        replace this := congr_arg Subtype.val this
        convert this
        · rw [that]
          apply main
        · rw [that]
          apply main
        · dsimp
          unfold List.rget
          dsimp!
          simp_rw [Nat.succ_sub_one, Nat.sub_self]
          rfl


lemma Game_World.History_of_staged_rtake (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal hist)
  (f_strat : g.fStrat_wHist hist leg) (s_strat : g.sStrat_wHist hist leg)
  (n : Nat) (nbnd : n < hist.length) :
  (g.hist_on_turn f_strat.val s_strat.val n).val = hist.rtake n := by
  induction' hist with x l ih
  · dsimp at nbnd
    contradiction
  · rw [List.rtake_cons_eq_self (by rw [List.length_cons, Nat.lt_succ] at nbnd ; exact nbnd)]
    cases' leg
    rename_i sofar now
    have st_1 : g.fStrat_staged (f_strat.val) l sofar := by
      split_ifs at now with T
      · apply g.fStrat_staged_cons_3 _ x l sofar now rfl T f_strat.prop
      · rw [Turn_not_fst_iff_snd] at T
        apply g.fStrat_staged_cons_4 _ x l sofar now rfl T f_strat.prop
    have st_2 : g.sStrat_staged (s_strat.val) l sofar := by
      split_ifs at now with T
      · apply g.sStrat_staged_cons_3 _ x l sofar now rfl T s_strat.prop
      · rw [Turn_not_fst_iff_snd] at T
        apply g.sStrat_staged_cons_1 _ x l sofar now rfl T s_strat.prop
    by_cases q : n < List.length l
    · exact ih sofar ⟨f_strat.val, st_1⟩ ⟨s_strat.val, st_2⟩ q
    · replace q : n = l.length := by apply Nat.eq_of_le_of_lt_succ (not_lt.mp q) nbnd
      rw [q, List.rtake_length]
      have := g.History_of_staged_length l sofar ⟨f_strat.val, st_1⟩ ⟨s_strat.val, st_2⟩
      convert this


noncomputable
def Game_World.fStrat_winner [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist +1))
  (main : ∀ (f_act : β) (al : g.snd_legal hist f_act), g.is_fst_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg)) :
  g.fStrat_wHist hist leg :=
  ⟨fun h ht hl =>
      if M : ((hist.rtake h.length) <:+ h)
      then
        if L : (h.length < hist.length)
        then ⟨hist.rget ⟨h.length, L⟩, (by convert g.hist_legal_rtake_fst hist h.length ht L leg ; rw [eq_comm] ; apply List.eq_of_suffix_of_length_eq M ; rw [List.length_rtake (le_of_lt L)])⟩
        else
          let f_act := h.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con] at T ; exact T ht)⟩
          have f_act_leg : g.snd_legal hist f_act := by
            convert g.hist_legal_rtake_snd h hist.length T _ hl
            · rw [not_lt] at L
              apply List.rtake_suffix_comm M L
            · apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con] at T ; exact T ht
          (Classical.choose (main f_act f_act_leg)).val h ht hl
      else ⟨Classical.choose ((hg h hl).1 ht), Classical.choose_spec ((hg h hl).1 ht)⟩
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos, dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact hl'
    · rw [List.length_rtake (le_of_lt hl')]
      exact Exists.intro [] rfl
   )⟩


noncomputable
def Game_World.sStrat_winner [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : Turn_fst (List.length hist +1))
  (main : ∀ (f_act : β) (al : g.fst_legal hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg)) :
  g.sStrat_wHist hist leg :=
  ⟨fun h ht hl =>
      if M : ((hist.rtake h.length) <:+ h)
      then
        if L : (h.length < hist.length)
        then ⟨hist.rget ⟨h.length, L⟩, (by convert g.hist_legal_rtake_snd hist h.length ht L leg ; rw [eq_comm] ; apply List.eq_of_suffix_of_length_eq M ; rw [List.length_rtake (le_of_lt L)])⟩
        else
          let f_act := h.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T ht)⟩
          have f_act_leg : g.fst_legal hist f_act := by
            convert g.hist_legal_rtake_fst h hist.length T _ hl
            · rw [not_lt] at L
              apply List.rtake_suffix_comm M L
            · apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T ht
          (Classical.choose (main f_act f_act_leg)).val h ht hl
      else ⟨Classical.choose ((hg h hl).2 ht), Classical.choose_spec ((hg h hl).2 ht)⟩
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos, dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact hl'
    · rw [List.length_rtake (le_of_lt hl')]
      exact Exists.intro [] rfl
   )⟩



def Game_World.fStrat_winner' [DecidableEq β] (g : Game_World α β)
  (hg : g.cPlayable_fst)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist +1))
  (select : (f_act : β) → (al : g.snd_legal hist f_act) →
      let leg' := (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg)
      g.fStrat_wHist (f_act :: hist) leg')
  -- (select_prop : ∀ (f_act : β) (al : g.snd_legal hist f_act),
  --       let leg' := (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg)
  --       ∀ snd_s : g.sStrat_wHist (f_act :: hist) leg', ({g with fst_strat := (select f_act al).val, snd_strat := snd_s.val} : Game α β).fst_win)
  :
  g.fStrat_wHist hist leg :=
  ⟨fun h ht hl =>
      if M : ((hist.rtake h.length) <:+ h)
      then
        if L : (h.length < hist.length)
        then ⟨hist.rget ⟨h.length, L⟩, (by convert g.hist_legal_rtake_fst hist h.length ht L leg ; rw [eq_comm] ; apply List.eq_of_suffix_of_length_eq M ; rw [List.length_rtake (le_of_lt L)])⟩
        else
          let f_act := h.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con] at T ; exact T ht)⟩
          have f_act_leg : g.snd_legal hist f_act := by
            convert g.hist_legal_rtake_snd h hist.length T _ hl
            · rw [not_lt] at L
              apply List.rtake_suffix_comm M L
            · apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con] at T ; exact T ht
          ((select f_act f_act_leg)).val h ht hl
      else hg h hl ht
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos, dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact hl'
    · rw [List.length_rtake (le_of_lt hl')]
      exact Exists.intro [] rfl
   )⟩


def Game_World.sStrat_winner' [DecidableEq β] (g : Game_World α β)
  (hg : g.cPlayable_snd)
  (hist : List β) (leg : g.hist_legal hist) (T : Turn_fst (List.length hist +1))
  (select : (f_act : β) → (al : g.fst_legal hist f_act) →
      let leg' := (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg)
      g.sStrat_wHist (f_act :: hist) leg')
  -- (select_prop : ∀ (f_act : β) (al : g.snd_legal hist f_act),
  --       let leg' := (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg)
  --       ∀ snd_s : g.sStrat_wHist (f_act :: hist) leg', ({g with fst_strat := (select f_act al).val, snd_strat := snd_s.val} : Game α β).fst_win)
  :
  g.sStrat_wHist hist leg :=
  ⟨fun h ht hl =>
      if M : ((hist.rtake h.length) <:+ h)
      then
        if L : (h.length < hist.length)
        then ⟨hist.rget ⟨h.length, L⟩, (by convert g.hist_legal_rtake_snd hist h.length ht L leg ; rw [eq_comm] ; apply List.eq_of_suffix_of_length_eq M ; rw [List.length_rtake (le_of_lt L)])⟩
        else
          let f_act := h.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T ht)⟩
          have f_act_leg : g.fst_legal hist f_act := by
            convert g.hist_legal_rtake_fst h hist.length T _ hl
            · rw [not_lt] at L
              apply List.rtake_suffix_comm M L
            · apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T ht
          ((select f_act f_act_leg)).val h ht hl
      else hg h hl ht
   ,
   (by
    intro t' hl' ht'
    dsimp
    rw [dif_pos, dif_pos]
    · congr
      rw [List.length_rtake (le_of_lt hl')]
    · rw [List.length_rtake (le_of_lt hl')]
      exact hl'
    · rw [List.length_rtake (le_of_lt hl')]
      exact Exists.intro [] rfl
   )⟩



lemma Game_World.fStrat_staged_cons_f_act (g : Game_World α β) (f_strat : g.fStrategy)
  (hist : List β) (leg : g.hist_legal hist) (T : Turn_fst (List.length hist + 1))
  (st : g.fStrat_staged f_strat hist leg) :
  let f_act := f_strat hist T leg ;
  g.fStrat_staged f_strat (f_act.val :: hist) (Game_World.hist_legal.cons hist f_act.val (by rw [if_pos T] ; exact f_act.prop) leg) := by
  intro f_act t' t'l t'f
  by_cases t'l' : t' < hist.length
  · specialize st t' t'l' t'f
    convert st using 2
    · funext _ ; rw [List.rtake_cons_eq_self] ; exact le_of_lt t'l'
    · rw [List.rtake_cons_eq_self] ; exact le_of_lt t'l'
    · funext _ ; rw [List.rtake_cons_eq_self] ; exact le_of_lt t'l'
    · apply @List.rget_cons_eq_self _ hist f_act.val ⟨t', t'l'⟩
  · rw [List.length_cons, Nat.lt_succ] at t'l
    rw [not_lt] at t'l'
    apply Subtype.eq
    dsimp
    simp_rw [le_antisymm t'l t'l']
    rw [List.rget_cons_length]
    congr
    · rw [List.rtake_cons_eq_self (le_of_eq (le_antisymm t'l t'l')), le_antisymm t'l t'l', List.rtake_length ]
    · rw [List.rtake_cons_eq_self (le_of_eq (le_antisymm t'l t'l')), le_antisymm t'l t'l', List.rtake_length ]
    · apply heq_prop
    · apply heq_prop


lemma Game_World.sStrat_staged_cons_f_act (g : Game_World α β) (s_strat : g.sStrategy)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist + 1))
  (st : g.sStrat_staged s_strat hist leg) :
  let f_act := s_strat hist T leg ;
  g.sStrat_staged s_strat (f_act.val :: hist) (Game_World.hist_legal.cons hist f_act.val (by rw [if_neg T] ; exact f_act.prop) leg) := by
  intro f_act t' t'l t'f
  by_cases t'l' : t' < hist.length
  · specialize st t' t'l' t'f
    convert st using 2
    · funext _ ; rw [List.rtake_cons_eq_self] ; exact le_of_lt t'l'
    · rw [List.rtake_cons_eq_self] ; exact le_of_lt t'l'
    · funext _ ; rw [List.rtake_cons_eq_self] ; exact le_of_lt t'l'
    · apply @List.rget_cons_eq_self _ hist f_act.val ⟨t', t'l'⟩
  · rw [List.length_cons, Nat.lt_succ] at t'l
    rw [not_lt] at t'l'
    apply Subtype.eq
    dsimp
    simp_rw [le_antisymm t'l t'l']
    rw [List.rget_cons_length]
    congr
    · rw [List.rtake_cons_eq_self (le_of_eq (le_antisymm t'l t'l')), le_antisymm t'l t'l', List.rtake_length ]
    · rw [List.rtake_cons_eq_self (le_of_eq (le_antisymm t'l t'l')), le_antisymm t'l t'l', List.rtake_length ]
    · apply heq_prop
    · apply heq_prop

lemma Game_World.sStrat_wHist_eq_of_eq_after (g : Game_World α β)
  (act : β) (hist : List β)
  (leg : g.hist_legal (hist)) (al : g.fst_legal hist act) (T : Turn_fst (List.length hist + 1))
  (s_strat : g.sStrat_wHist hist leg) (snd_s : g.sStrat_wHist (act :: hist) (Game_World.hist_legal.cons hist act (by rw [if_pos T] ; exact al) leg))
  (f_strat : g.fStrat_wHist hist leg) (n : Nat) (tu : Turn_snd (n+1))
  (main : let h := g.hist_on_turn f_strat.val s_strat.val n
          let H := g.hist_on_turn f_strat.val snd_s.val n
      n ≥ hist.length → (s_strat.val h.val (by rw [h.prop.2] ; exact tu) h.prop.1).val = (snd_s.val H.val (by rw [H.prop.2] ; exact tu)  H.prop.1).val ) :
  let h := g.hist_on_turn f_strat.val s_strat.val n
  let H := g.hist_on_turn f_strat.val snd_s.val n
  (s_strat.val h.val (by rw [h.prop.2] ; exact tu) h.prop.1).val = (snd_s.val H.val (by rw [H.prop.2] ; exact tu)  H.prop.1).val :=
  by
  intro h H
  by_cases q : n ≥ List.length hist
  · exact main q
  · push_neg at q
    have := s_strat.prop n q tu
    have that := snd_s.prop n (lt_trans q (Nat.lt_succ_self _) ) tu
    replace this := congr_arg Subtype.val this
    replace that := congr_arg Subtype.val that
    dsimp at this that
    rw [@List.rget_cons_eq_self _ hist act ⟨n,q⟩] at that
    rw [← that] at this
    convert this
    · rw [g.History_of_staged_rtake hist leg _ _ _ q]
    · rw [g.History_of_staged_rtake hist leg _ _ _ q]
    · rw [List.rtake_cons_eq_self (le_of_lt q), g.History_of_staged_rtake hist leg _ ⟨snd_s.val, g.sStrat_staged_cons_3 _ act hist leg al rfl T snd_s.prop⟩ _ q]
    · rw [List.rtake_cons_eq_self (le_of_lt q), g.History_of_staged_rtake hist leg _ ⟨snd_s.val, g.sStrat_staged_cons_3 _ act hist leg al rfl T snd_s.prop⟩ _ q]

lemma Game_World.fStrat_wHist_eq_of_eq_after (g : Game_World α β)
  (act : β) (hist : List β)
  (leg : g.hist_legal (hist)) (al : g.snd_legal hist act) (T : ¬ Turn_fst (List.length hist + 1))
  (s_strat : g.fStrat_wHist hist leg) (snd_s : g.fStrat_wHist (act :: hist) (Game_World.hist_legal.cons hist act (by rw [if_neg T] ; exact al) leg))
  (f_strat : g.sStrat_wHist hist leg) (n : Nat) (tu : Turn_fst (n+1))
  (main : let h := g.hist_on_turn s_strat.val f_strat.val n
          let H := g.hist_on_turn snd_s.val f_strat.val n
      n ≥ hist.length → (s_strat.val h.val (by rw [h.prop.2] ; exact tu) h.prop.1).val = (snd_s.val H.val (by rw [H.prop.2] ; exact tu)  H.prop.1).val ) :
  let h := g.hist_on_turn s_strat.val f_strat.val n
  let H := g.hist_on_turn snd_s.val f_strat.val n
  (s_strat.val h.val (by rw [h.prop.2] ; exact tu) h.prop.1).val = (snd_s.val H.val (by rw [H.prop.2] ; exact tu)  H.prop.1).val :=
  by
  intro h H
  by_cases q : n ≥ List.length hist
  · exact main q
  · push_neg at q
    have := s_strat.prop n q tu
    have that := snd_s.prop n (lt_trans q (Nat.lt_succ_self _) ) tu
    replace this := congr_arg Subtype.val this
    replace that := congr_arg Subtype.val that
    dsimp at this that
    rw [@List.rget_cons_eq_self _ hist act ⟨n,q⟩] at that
    rw [← that] at this
    convert this
    · rw [g.History_of_staged_rtake hist leg _ _ _ q]
    · rw [g.History_of_staged_rtake hist leg _ _ _ q]
    · rw [List.rtake_cons_eq_self (le_of_lt q), g.History_of_staged_rtake hist leg ⟨snd_s.val, g.fStrat_staged_cons_4 _ act hist leg al rfl T snd_s.prop⟩ _ _ q]
    · rw [List.rtake_cons_eq_self (le_of_lt q), g.History_of_staged_rtake hist leg ⟨snd_s.val, g.fStrat_staged_cons_4 _ act hist leg al rfl T snd_s.prop⟩ _ _ q]


lemma Game_World.Strat_wHist_f_act_cons_eq_History_on_turn_length (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (f_strat : g.fStrat_wHist hist leg) (s_strat : g.sStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  (g.hist_on_turn f_strat.val s_strat.val (hist.length+1)).val = (f_act.val :: hist) := by
  intro f_act
  dsimp [hist_on_turn]
  rw [dif_pos T]
  dsimp
  congr
  · rw [g.History_of_staged_length]
  · rw [Subtype.heq_iff_coe_eq]
    · apply fStrat_eq_of_hist_eq
      rw [g.History_of_staged_length]
    · intro _
      simp_rw [g.History_of_staged_length]
  · rw [g.History_of_staged_length]


private lemma Game_World.Strat_wHist_f_act_cons_suffix_Hist_helper  (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (f_strat : g.fStrat_wHist hist leg) (s_strat : g.sStrat_wHist hist leg)
  (n : Nat) (n_bnd : n ≥ hist.length + 1):
  let f_act := f_strat.val hist T leg
  (f_act.val :: hist) <:+ g.hist_on_turn f_strat.val s_strat.val (n) :=
  by
  intro f_act
  rw [← Strat_wHist_f_act_cons_eq_History_on_turn_length g hist leg T f_strat s_strat]
  apply g.hist_on_turn_suffix
  exact n_bnd


lemma Game_World.Strat_wHist_f_act_cons_suffix_Hist (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (f_strat : g.fStrat_wHist hist leg) (s_strat : g.sStrat_wHist hist leg)
  (n : Nat) (tu : Turn_snd (n+1)) (n_bnd : n ≥ hist.length):
  let f_act := f_strat.val hist T leg
  (f_act.val :: hist) <:+ g.hist_on_turn f_strat.val s_strat.val n :=
  by
  intro f_act
  simp_rw [le_iff_eq_or_lt] at n_bnd
  cases' n_bnd with nb nb
  · rw [nb, Turn_fst_iff_not_snd] at T
    exfalso
    exact T tu
  · rw [Nat.lt_iff_add_one_le] at nb
    apply Strat_wHist_f_act_cons_suffix_Hist_helper
    exact nb


lemma Game_World.Strat_wHist_s_act_cons_eq_History_on_turn_length (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal (hist)) (T : ¬ Turn_fst (List.length hist + 1))
  (f_strat : g.sStrat_wHist hist leg) (s_strat : g.fStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  (g.hist_on_turn s_strat.val f_strat.val (hist.length+1)).val = (f_act.val :: hist) := by
  intro f_act
  dsimp [hist_on_turn]
  rw [dif_neg T]
  dsimp
  congr
  · rw [g.History_of_staged_length]
  · rw [Subtype.heq_iff_coe_eq]
    · apply sStrat_eq_of_hist_eq
      rw [g.History_of_staged_length]
    · intro _
      simp_rw [g.History_of_staged_length]
  · rw [g.History_of_staged_length]


private lemma Game_World.Strat_wHist_s_act_cons_suffix_Hist_helper  (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal (hist)) (T : ¬ Turn_fst (List.length hist + 1))
  (f_strat : g.sStrat_wHist hist leg) (s_strat : g.fStrat_wHist hist leg)
  (n : Nat) (n_bnd : n ≥ hist.length + 1):
  let f_act := f_strat.val hist T leg
  (f_act.val :: hist) <:+ g.hist_on_turn s_strat.val f_strat.val (n) :=
  by
  intro f_act
  rw [← Strat_wHist_s_act_cons_eq_History_on_turn_length g hist leg T f_strat s_strat]
  apply g.hist_on_turn_suffix
  exact n_bnd


lemma Game_World.Strat_wHist_s_act_cons_suffix_Hist (g : Game_World α β)
  (hist : List β) (leg : g.hist_legal (hist)) (T : ¬ Turn_fst (List.length hist + 1))
  (f_strat : g.sStrat_wHist hist leg) (s_strat : g.fStrat_wHist hist leg)
  (n : Nat) (tu : Turn_fst (n+1)) (n_bnd : n ≥ hist.length):
  let f_act := f_strat.val hist T leg
  (f_act.val :: hist) <:+ g.hist_on_turn s_strat.val f_strat.val n :=
  by
  intro f_act
  simp_rw [le_iff_eq_or_lt] at n_bnd
  cases' n_bnd with nb nb
  · rw [nb] at T
    exfalso
    exact T tu
  · rw [Nat.lt_iff_add_one_le] at nb
    apply Strat_wHist_s_act_cons_suffix_Hist_helper
    exact nb

private lemma Game_World.sStrat_winner_help_rget [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : g.hist_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : g.fStrat_wHist hist leg) {n : Nat} (n_bnd : n ≥ List.length hist) (tu : Turn_snd (n+1))
  (difp_2 : ¬ List.length (g.hist_on_turn (f_strat.val) ((sStrat_winner g hg hist leg T main).val) n).val < List.length hist) :
  let h := (g.hist_on_turn f_strat.val (sStrat_winner g hg hist leg T main).val n)
  h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩ = (f_strat.val hist T leg).val :=
  by
  intro h
  rw [List.rget_suffix (Strat_wHist_f_act_cons_suffix_Hist g hist leg T _ _ n tu n_bnd) ⟨hist.length, (by rw [List.length_cons] ; apply Nat.lt_succ_self)⟩]
  rw [List.rget_cons_length]

private lemma Game_World.fStrat_winner_help_rget [DecidableEq β] (g : Game_World α β) (hg : g.playable)

  (hist : List β) (leg : g.hist_legal (hist)) (T : ¬ Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.snd_legal hist f_act), g.is_fst_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg))
  (f_strat : g.sStrat_wHist hist leg) {n : Nat} (n_bnd : n ≥ List.length hist) (tu : Turn_fst (n+1))
  (difp_2 : ¬ List.length (g.hist_on_turn ((g.fStrat_winner hg hist leg T main).val) (f_strat.val) n).val < List.length hist) :
  let h := (g.hist_on_turn (g.fStrat_winner hg hist leg T main).val f_strat.val n)
  h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩ = (f_strat.val hist T leg).val :=
  by
  intro h
  rw [List.rget_suffix (Strat_wHist_s_act_cons_suffix_Hist g hist leg T _ _ n tu n_bnd) ⟨hist.length, (by rw [List.length_cons] ; apply Nat.lt_succ_self)⟩]
  rw [List.rget_cons_length]


private lemma Game_World.sStrat_winner_help_History [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : g.fStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val = g.hist_on_turn f_strat.val ws.val :=
  by
  intro f_act ws
  funext n
  induction' n with n ih
  · rfl
  · dsimp [Game_World.hist_on_turn]
    split_ifs with tu
    · apply Subtype.eq
      dsimp!
      congr 1
      · apply g.fStrat_eq_of_hist_eq
        rw [ih]
      · rw [ih]
    · rw [Turn_not_fst_iff_snd] at tu
      apply Subtype.eq
      dsimp!
      -- refactore start here
      congr 1
      · apply g.sStrat_wHist_eq_of_eq_after f_act.val hist leg f_act.prop T _ _ _ n tu
        intro h H n_bnd
        dsimp [Game_World.sStrat_winner]
        have difp_1 : hist.rtake (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val.length <:+ (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val :=
          by
          simp_rw [g.hist_on_turn_length]
          apply List.IsSuffix.trans _ (g.Strat_wHist_f_act_cons_suffix_Hist hist leg T f_strat (g.sStrat_winner hg hist leg T main) n tu n_bnd)
          rw [List.rtake_all_of_le n_bnd]
          apply List.suffix_cons
        rw [dif_pos]
        swap
        · apply difp_1
        · have difp_2 : ¬ (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val.length < hist.length :=
            by
            simp_rw [g.hist_on_turn_length, not_lt]
            exact n_bnd
          rw [dif_neg]
          swap
          · apply difp_2
          · apply g.sStrat_eq_of_strat_hist_eq
            · let h := (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n)
              let f_act := h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩
              have f_act_leg : g.fst_legal hist f_act := by
                convert g.hist_legal_rtake_fst h hist.length T _ h.prop.1
                · rw [not_lt] at difp_2
                  apply List.rtake_suffix_comm difp_1 difp_2
                · apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu)
              apply @Classical.choose_congr_surgery _ _ _
                  (fun ws :
                    g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg)  =>
                      ∀ fst_s : g.fStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg),
                      ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win)
                  (fun ws :
                    g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg)  =>
                      ∀ fst_s : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg),
                      ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win)
                  (main f_act f_act_leg)
                  (main (f_strat.val hist T leg).val (f_strat.val hist T leg).prop)
                  (fun ws : g.sStrategy  =>
                      ∀ fst_s : g.fStrat_wHist  (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg),
                      ({g with fst_strat := fst_s.val, snd_strat := ws} : Game α β).snd_win)
                  (fun ws : g.sStrategy =>
                      ∀ fst_s : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg),
                      ({g with fst_strat := fst_s.val, snd_strat := ws} : Game α β).snd_win)
              -- survived dtt hell
              · intro ws ; rfl
              · intro ws ; rfl
              · intro ws
                have := g.sStrat_winner_help_rget hg hist leg T main f_strat n_bnd tu difp_2
                simp_rw [this]
              · intro ws
                constructor
                · intro W fs
                  convert W ⟨fs.val, (by simp_rw [g.sStrat_winner_help_rget hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
                · intro W fs
                  convert W ⟨fs.val, (by simp_rw [← g.sStrat_winner_help_rget hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
            · replace ih := congr_arg Subtype.val ih
              convert ih
      · replace ih := congr_arg Subtype.val ih
        exact ih


lemma Game_World.fStrat_winner_help_History [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.snd_legal hist f_act), g.is_fst_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg))
  (f_strat : g.sStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val = g.hist_on_turn ws.val f_strat.val :=
  by
  intro f_act ws
  funext n
  induction' n with n ih
  · rfl
  · dsimp [ hist_on_turn]
    split_ifs with tu
    · apply Subtype.eq
      dsimp!
      -- refactore start here
      congr 1
      · apply fStrat_wHist_eq_of_eq_after g f_act.val hist leg f_act.prop T _ _ _ n tu
        intro h H n_bnd
        dsimp [fStrat_winner]
        have difp_1 : hist.rtake (g.hist_on_turn  (fStrat_winner g hg hist leg T main).val f_strat.val n).val.length <:+ (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val n).val :=
          by
          simp_rw [g.hist_on_turn_length]
          apply List.IsSuffix.trans _ (g.Strat_wHist_s_act_cons_suffix_Hist hist leg T f_strat (g.fStrat_winner hg hist leg T main) n tu n_bnd)
          rw [List.rtake_all_of_le n_bnd]
          apply List.suffix_cons
        have difp_2 : ¬ (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val n).val.length < hist.length :=
            by
            simp_rw [g.hist_on_turn_length, not_lt]
            exact n_bnd
        rw [dif_pos]
        swap
        · apply difp_1
        · rw [dif_neg]
          swap
          · apply difp_2
          · apply fStrat_eq_of_strat_hist_eq
            · let h := (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val n)
              let f_act := h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩
              have f_act_leg : g.snd_legal hist f_act := by
                convert g.hist_legal_rtake_snd h hist.length T _ h.prop.1
                · rw [not_lt] at difp_2
                  apply List.rtake_suffix_comm difp_1 difp_2
                · apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con] at T ; exact T (by rw [h.prop.2] ; exact tu)
              apply @Classical.choose_congr_surgery _ _ _
                  (fun ws : g.fStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact f_act_leg) leg)  =>
                      ∀ fst_s : g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact f_act_leg) leg),
                      ({g with fst_strat := ws.val, snd_strat := fst_s.val} : Game α β).fst_win)
                  (fun ws : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_neg T] ; exact (f_strat.val hist T leg).prop) leg)  =>
                      ∀ fst_s : g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_neg T] ; exact (f_strat.val hist T leg).prop) leg),
                      ({g with fst_strat := ws.val, snd_strat := fst_s.val} : Game α β).fst_win)
                  (main f_act f_act_leg)
                  (main (f_strat.val hist T leg).val (f_strat.val hist T leg).prop)
                  (fun ws : g.fStrategy  =>
                      ∀ fst_s : g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact f_act_leg) leg),
                      ({g with fst_strat := ws, snd_strat := fst_s.val} : Game α β).fst_win)
                  (fun ws : g.fStrategy =>
                      ∀ fst_s : g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_neg T] ; exact (f_strat.val hist T leg).prop) leg),
                      ({g with fst_strat := ws, snd_strat := fst_s.val} : Game α β).fst_win)
              -- survived dtt hell
              · intro ws ; rfl
              · intro ws ; rfl
              · intro ws
                have := fStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2
                simp_rw [this]
              · intro ws
                constructor
                · intro W fs
                  convert W ⟨fs.val, (by simp_rw [fStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
                · intro W fs
                  convert W ⟨fs.val, (by simp_rw [← fStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
            · replace ih := congr_arg Subtype.val ih
              convert ih
      · replace ih := congr_arg Subtype.val ih
        exact ih
    · apply Subtype.eq
      dsimp!
      congr 1
      · apply sStrat_eq_of_hist_eq
        rw [ih]
      · rw [ih]


lemma Game_World.sStrat_winner_help_history [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal  hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : g.fStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val = g.hist_on_turn f_strat.val ws.val :=
  by
  intro f_act _
  apply g.sStrat_winner_help_History

lemma fStrat_winner_help_history [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.snd_legal  hist f_act), g.is_fst_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg))
  (f_strat : g.sStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.hist_on_turn (g.fStrat_winner hg hist leg T main).val f_strat.val = g.hist_on_turn ws.val f_strat.val :=
  by
  intro f_act _
  apply g.fStrat_winner_help_History



lemma Game_World.fStrat_winner_help_state [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.snd_legal  hist f_act), g.is_fst_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg))
  (f_strat : g.sStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.state_on_turn (g.fStrat_winner hg hist leg T main).val f_strat.val = g.state_on_turn ws.val f_strat.val :=
  by
  intro f_act ws
  funext n
  cases' n with n
  · rfl
  · dsimp [Game_World.state_on_turn]
    split_ifs with tu
    · simp_rw [fStrat_winner_help_history]
      congr
      · funext _ ; simp_rw [fStrat_winner_help_history]
      · rw [Subtype.heq_iff_coe_eq]
        · -- refactor wrt ↑ from here
          apply fStrat_wHist_eq_of_eq_after g f_act.val hist leg f_act.prop T _ _ _ n tu
          intro h H n_bnd
          dsimp [fStrat_winner]
          have difp_1 : hist.rtake (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val  n).val.length <:+ (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val  n).val :=
            by
            simp_rw [g.hist_on_turn_length]
            apply List.IsSuffix.trans _ (Strat_wHist_s_act_cons_suffix_Hist g hist leg T f_strat (fStrat_winner g hg hist leg T main) n tu n_bnd)
            rw [List.rtake_all_of_le n_bnd]
            apply List.suffix_cons
          rw [dif_pos]
          swap
          · apply difp_1
          · have difp_2 : ¬ (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val n).val.length < hist.length :=
              by
              simp_rw [g.hist_on_turn_length, not_lt]
              exact n_bnd
            rw [dif_neg]
            swap
            · apply difp_2
            · apply fStrat_eq_of_strat_hist_eq
              · let h := (g.hist_on_turn (fStrat_winner g hg hist leg T main).val f_strat.val n)
                let f_act := h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩
                have f_act_leg : g.snd_legal hist f_act := by
                  convert g.hist_legal_rtake_snd  h hist.length T _ h.prop.1
                  · rw [not_lt] at difp_2
                    apply List.rtake_suffix_comm difp_1 difp_2
                  · apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con] at T ; exact T (by rw [h.prop.2] ; exact tu)
                apply @Classical.choose_congr_surgery _ _ _
                    (fun ws : g.fStrat_wHist  (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact f_act_leg) leg)  =>
                        ∀ fst_s : g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact f_act_leg) leg),
                        ({g with fst_strat := ws.val, snd_strat := fst_s.val} : Game α β).fst_win)
                    (fun ws : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_neg T] ; exact (f_strat.val hist T leg).prop) leg)  =>
                        ∀ fst_s : g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_neg T] ; exact (f_strat.val hist T leg).prop) leg),
                        ({g with fst_strat := ws.val, snd_strat := fst_s.val} : Game α β).fst_win)
                    (main f_act f_act_leg)
                    (main (f_strat.val hist T leg).val (f_strat.val hist T leg).prop)
                    (fun ws : g.fStrategy  =>
                        ∀ fst_s : g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact f_act_leg) leg),
                        ({g with fst_strat := ws, snd_strat := fst_s.val} : Game α β).fst_win)
                    (fun ws : g.fStrategy =>
                        ∀ fst_s : g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_neg T] ; exact (f_strat.val hist T leg).prop) leg),
                        ({g with fst_strat := ws, snd_strat := fst_s.val} : Game α β).fst_win)
                -- survived dtt hell
                · intro ws ; rfl
                · intro ws ; rfl
                · intro ws
                  have := fStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2
                  simp_rw [this]
                · intro ws
                  constructor
                  · intro W fs
                    convert W ⟨fs.val, (by simp_rw [fStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
                  · intro W fs
                    convert W ⟨fs.val, (by simp_rw [← fStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
              · have := fStrat_winner_help_history g hg hist leg T main f_strat
                dsimp [Game_World.hist_on_turn] at this
                rw [Function.funext_iff] at this
                replace this := congr_arg Subtype.val (this n)
                convert this
        · intro _ ; simp_rw [fStrat_winner_help_history]
    · simp_rw [fStrat_winner_help_history]
      congr
      · funext _ ; simp_rw [fStrat_winner_help_history]
      · rw [Subtype.heq_iff_coe_eq]
        · apply sStrat_eq_of_hist_eq
          simp_rw [fStrat_winner_help_history]
        · intro _ ; simp_rw [fStrat_winner_help_history]




-- private lemma refactor_4 [DecidableEq β] (g : Game_World α β)
--
--     (hg : g.playable) (hist : List β) (leg : g.hist_legal hist) (T : Turn_fst (List.length hist + 1))
--     (main : ∀ (f_act : β) (al : g.fst_legal hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
--     (f_strat : g.fStrat_wHist hist leg) {n : ℕ}
--     (tu : Turn_snd (n + 1)) :
--     let f_act := f_strat.val hist T leg
--     let ws := Classical.choose (main f_act.val f_act.prop)
--     let h := g.hist_on_turn (f_strat.val) ((g.sStrat_winner hg hist leg T main).val) n
--     (ih : h = g.hist_on_turn (f_strat.val) (ws.val) n) →
--     ((g.sStrat_winner hg hist leg T main).val (g.hist_on_turn (f_strat.val) ((g.sStrat_winner hg hist leg T main).val) n).val
--         (by rw [h.prop.2] ; exact tu)
--         (h.prop.1)).val :: h.val =
--     let H := g.hist_on_turn f_strat.val (Classical.choose (main f_act.val f_act.prop)).val n
--     ((Classical.choose (main f_act.val f_act.prop)).val H.val (by rw [H.prop.2] ; exact tu) H.prop.1).val :: H.val :=
--     by
--     intro f_act ws h ih
--     congr 1
--     · apply g.sStrat_wHist_eq_of_eq_after f_act.val hist leg f_act.prop T _ _ _ n tu
--       intro h H n_bnd
--       dsimp [Game_World.sStrat_winner]
--       have difp_1 : hist.rtake (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val.length <:+ (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val :=
--         by
--         simp_rw [g.hist_on_turn_length]
--         apply List.IsSuffix.trans _ (g.Strat_wHist_f_act_cons_suffix_Hist hist leg T f_strat (g.sStrat_winner hg hist leg T main) n tu n_bnd)
--         rw [List.rtake_all_of_le n_bnd]
--         apply List.suffix_cons
--       rw [dif_pos]
--       swap
--       · apply difp_1
--       · have difp_2 : ¬ (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val.length < hist.length :=
--           by
--           simp_rw [g.hist_on_turn_length, not_lt]
--           exact n_bnd
--         rw [dif_neg]
--         swap
--         · apply difp_2
--         · apply g.sStrat_eq_of_strat_hist_eq
--           · let h := (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n)
--             let f_act := h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩
--             have f_act_leg : g.fst_legal hist f_act := by
--               convert g.hist_legal_rtake_fst h hist.length T _ h.prop.1
--               · rw [not_lt] at difp_2
--                 apply List.rtake_suffix_comm difp_1 difp_2
--               · apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu)
--             apply @Classical.choose_congr_surgery _ _ _
--                 (fun ws :
--                   g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg)  =>
--                     ∀ fst_s : g.fStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg),
--                     ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win)
--                 (fun ws :
--                   g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg)  =>
--                     ∀ fst_s : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg),
--                     ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win)
--                 (main f_act f_act_leg)
--                 (main (f_strat.val hist T leg).val (f_strat.val hist T leg).prop)
--                 (fun ws : g.sStrategy  =>
--                     ∀ fst_s : g.fStrat_wHist  (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg),
--                     ({g with fst_strat := fst_s.val, snd_strat := ws} : Game α β).snd_win)
--                 (fun ws : g.sStrategy =>
--                     ∀ fst_s : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg),
--                     ({g with fst_strat := fst_s.val, snd_strat := ws} : Game α β).snd_win)
--             -- survived dtt hell
--             · intro ws ; rfl
--             · intro ws ; rfl
--             · intro ws
--               have := g.sStrat_winner_help_rget hg hist leg T main f_strat n_bnd tu difp_2
--               simp_rw [this]
--             · intro ws
--               constructor
--               · intro W fs
--                 convert W ⟨fs.val, (by simp_rw [g.sStrat_winner_help_rget hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
--               · intro W fs
--                 convert W ⟨fs.val, (by simp_rw [← g.sStrat_winner_help_rget hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
--           · replace ih := congr_arg Subtype.val ih
--             convert ih
--     · replace ih := congr_arg Subtype.val ih
--       exact ih



private lemma Game_World.sStrat_winner_help_state [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : g.fStrat_wHist hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.state_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val = g.state_on_turn f_strat.val ws.val :=
  by
  intro f_act ws
  funext n
  cases' n with n
  · rfl
  · dsimp [Game_World.state_on_turn]
    split_ifs with tu
    · simp_rw [g.sStrat_winner_help_history]
      congr
      · funext _ ; simp_rw [g.sStrat_winner_help_history]
      · rw [Subtype.heq_iff_coe_eq]
        · apply g.fStrat_eq_of_hist_eq
          simp_rw [g.sStrat_winner_help_history]
        · intro _ ; simp_rw [g.sStrat_winner_help_history]
    · simp_rw [g.sStrat_winner_help_history]
      congr
      · funext _ ; simp_rw [g.sStrat_winner_help_history]
      · rw [Subtype.heq_iff_coe_eq]
        · -- refactor wrt ↑ from here
          apply g.sStrat_wHist_eq_of_eq_after f_act.val hist leg f_act.prop T _ _ _ n tu
          intro h H n_bnd
          dsimp [sStrat_winner]
          have difp_1 : hist.rtake (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val.length <:+ (g.hist_on_turn f_strat.val (sStrat_winner g hg hist leg T main).val n).val :=
            by
            simp_rw [g.hist_on_turn_length]
            apply List.IsSuffix.trans _ (g.Strat_wHist_f_act_cons_suffix_Hist hist leg T f_strat (g.sStrat_winner hg hist leg T main) n tu n_bnd)
            rw [List.rtake_all_of_le n_bnd]
            apply List.suffix_cons
          rw [dif_pos]
          swap
          · apply difp_1
          · have difp_2 : ¬ (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n).val.length < hist.length :=
              by
              simp_rw [g.hist_on_turn_length, not_lt]
              exact n_bnd
            rw [dif_neg]
            swap
            · apply difp_2
            · apply sStrat_eq_of_strat_hist_eq
              · let h := (g.hist_on_turn f_strat.val (g.sStrat_winner hg hist leg T main).val n)
                let f_act := h.val.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu))⟩
                have f_act_leg : g.fst_legal hist f_act := by
                  convert g.hist_legal_rtake_fst h hist.length T _ h.prop.1
                  · rw [not_lt] at difp_2
                    apply List.rtake_suffix_comm difp_1 difp_2
                  · apply lt_of_le_of_ne (not_lt.mp difp_2) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T (by rw [h.prop.2] ; exact tu)
                apply @Classical.choose_congr_surgery _ _ _
                    (fun ws : g.sStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg)  =>
                        ∀ fst_s : g.fStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg),
                        ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win)
                    (fun ws : g.sStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg)  =>
                        ∀ fst_s : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg),
                        ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win)
                    (main f_act f_act_leg)
                    (main (f_strat.val hist T leg).val (f_strat.val hist T leg).prop)
                    (fun ws : g.sStrategy  =>
                        ∀ fst_s : g.fStrat_wHist (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact f_act_leg) leg),
                        ({g with fst_strat := fst_s.val, snd_strat := ws} : Game α β).snd_win)
                    (fun ws : g.sStrategy =>
                        ∀ fst_s : g.fStrat_wHist ((f_strat.val hist T leg).val :: hist) (Game_World.hist_legal.cons hist (f_strat.val hist T leg).val (by rw [if_pos T] ; exact (f_strat.val hist T leg).prop) leg),
                        ({g with fst_strat := fst_s.val, snd_strat := ws} : Game α β).snd_win)
                -- survived dtt hell
                · intro ws ; rfl
                · intro ws ; rfl
                · intro ws
                  have := sStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2
                  simp_rw [this]
                · intro ws
                  constructor
                  · intro W fs
                    convert W ⟨fs.val, (by simp_rw [sStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
                  · intro W fs
                    convert W ⟨fs.val, (by simp_rw [← sStrat_winner_help_rget g hg hist leg T main f_strat n_bnd tu difp_2] ; exact fs.prop)⟩
              · have := sStrat_winner_help_history g hg hist leg T main f_strat
                dsimp [Game_World.hist_on_turn] at this
                rw [Function.funext_iff] at this
                replace this := congr_arg Subtype.val (this n)
                convert this
        · intro _ ; simp_rw [sStrat_winner_help_history]


lemma Game_World.sStrat_winner_wins [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal hist f_act), g.is_snd_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : g.fStrat_wHist hist leg) :
  ({g with fst_strat := f_strat.val, snd_strat := (g.sStrat_winner hg hist leg T main).val} : Game α β).snd_win :=
  by
  let f_act := f_strat.val hist T leg
  let ws_prop := Classical.choose_spec (main f_act.val f_act.prop)
  specialize ws_prop ⟨f_strat.val, (g.fStrat_staged_cons_f_act _ _ leg T f_strat.prop)⟩
  obtain ⟨τ, τw, τn⟩ := ws_prop
  dsimp at τw τn
  rw [Game.hist_on_turn, ← g.sStrat_winner_help_History hg hist leg T main f_strat] at τw
  use τ
  constructor
  · apply τw
  · intro t tl
    specialize τn t tl
    unfold Game.state_on_turn_neutral Game_World.state_on_turn_neutral
    unfold Game.state_on_turn_neutral Game_World.state_on_turn_neutral at τn
    intro twl
    cases' twl with wf ws
    · apply τn
      apply Game_World.Turn_isWL.wf
      rw [ ← g.sStrat_winner_help_History hg hist leg T main f_strat]
      apply wf
    · apply τn
      apply Game_World.Turn_isWL.ws
      rw [ ← g.sStrat_winner_help_History hg hist leg T main f_strat]
      apply ws



lemma fStrat_winner_wins [DecidableEq β] (g : Game_World α β)
  (hg : g.playable)
  (hist : List β) (leg : g.hist_legal hist) (T : ¬ Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.snd_legal hist f_act), g.is_fst_staged_win (f_act :: hist) (Game_World.hist_legal.cons hist f_act (by rw [if_neg T] ; exact al) leg))
  (f_strat : g.sStrat_wHist hist leg) :
  ({g with fst_strat := (g.fStrat_winner hg hist leg T main).val, snd_strat := f_strat.val} : Game α β).fst_win :=
  by
  let f_act := f_strat.val hist T leg
  let ws_prop := Classical.choose_spec (main f_act.val f_act.prop)
  specialize ws_prop ⟨f_strat.val, (g.sStrat_staged_cons_f_act _ _ leg T f_strat.prop)⟩
  obtain ⟨τ, τw, τn⟩ := ws_prop
  dsimp at τw τn
  rw [Game.hist_on_turn, ← g.fStrat_winner_help_History hg hist leg T main f_strat] at τw
  use τ
  constructor
  · apply τw
  · intro t tl
    specialize τn t tl
    unfold Game.state_on_turn_neutral Game_World.state_on_turn_neutral
    unfold Game.state_on_turn_neutral Game_World.state_on_turn_neutral at τn
    intro twl
    cases' twl with wf ws
    · apply τn
      apply Game_World.Turn_isWL.wf
      rw [ ← g.fStrat_winner_help_History hg hist leg T main f_strat]
      apply wf
    · apply τn
      apply Game_World.Turn_isWL.ws
      rw [ ← g.fStrat_winner_help_History hg hist leg T main f_strat]
      apply ws
