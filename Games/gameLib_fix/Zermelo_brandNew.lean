
import Games.gameLib_fix.Termination

open Lean

-- # To Mathlib

lemma List.length_rtake {l : List α} {t : Nat} (ht : t ≤ l.length) : (l.rtake t).length = t := by
  unfold List.rtake ; rw [List.length_drop] ; apply Nat.sub_sub_self ht

def List.rget (l : List α) (t : Fin l.length) := l.get ⟨l.length - 1 - t, (by rw [Nat.sub_sub] ; apply Nat.sub_lt_self (by apply Nat.add_pos_left ; exact zero_lt_one) (by rw [add_comm, Nat.succ_le] ; apply t.prop) )⟩

lemma List.rget_cons_rtake {l : List α} {t : Fin l.length} : l.rtake (t+1) = (l.rget t) :: (l.rtake t) := by
  unfold List.rtake List.rget
  rw [Nat.sub_succ', tsub_right_comm]
  cases' l with x l
  · have no := t.prop
    contradiction
  · simp_rw [List.length_cons, Nat.succ_sub_one]
    rw [show Nat.succ (length l) - ↑t = Nat.succ (length l - ↑t) from (by apply Nat.succ_sub ; have := t.prop ; simp_rw [List.length_cons] at this ; rw [Nat.lt_succ] at this ; exact this)]
    apply List.drop_eq_get_cons

lemma List.rtake_cons_eq_self {l : List α} {x : α} {t : Nat} (ht : t ≤ l.length) : ((x :: l).rtake t) = (l.rtake t) := by
  unfold List.rtake
  rw [List.length_cons, Nat.succ_sub ht]
  rfl


lemma List.rget_cons_eq_self {l : List α} {x : α} {t : Fin l.length} : (x :: l).rget ⟨t.val, (by rw [List.length_cons] ; apply lt_trans t.prop ; apply Nat.lt_succ_self) ⟩ = l.rget t := by
  unfold List.rget
  simp_rw [List.length_cons]
  simp_rw [Nat.succ_sub (show 1 ≤ l.length by by_contra! con ; rw [Nat.lt_one_iff] at con ; have := t.prop ; simp_rw [con] at this ; contradiction)]
  simp_rw [Nat.succ_sub (show t ≤ l.length - 1 by apply Nat.le_sub_one_of_lt ; exact t.prop)]
  rfl



-- # Staging

lemma Hist_legal_rtake_fst (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) (t : Nat) (htT : Turn_fst (t+1)) (htL : t < hist.length)
  (main : Hist_legal ini f_law s_law hist) : f_law ini (hist.rtake t) (hist.rget ⟨t, htL⟩) := by
  replace main := Hist_legal_rtake _ _ _ _ (t+1) main
  rw [@List.rget_cons_rtake _ _ ⟨t,htL⟩ ] at main
  cases' main
  rename_i _ now
  rw [List.length_rtake (le_of_lt htL)] at now
  rw [if_pos htT] at now
  exact now

lemma Hist_legal_rtake_snd (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) (t : Nat) (htT : Turn_snd (t+1)) (htL : t < hist.length)
  (main : Hist_legal ini f_law s_law hist) : s_law ini (hist.rtake t) (hist.rget ⟨t, htL⟩) := by
  replace main := Hist_legal_rtake _ _ _ _ (t+1) main
  rw [@List.rget_cons_rtake _ _ ⟨t,htL⟩ ] at main
  cases' main
  rename_i _ now
  rw [List.length_rtake (le_of_lt htL)] at now
  rw [Turn_snd_iff_not_fst] at htT
  rw [if_neg htT] at now
  exact now



def fStrat_staged (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (hist : List β) (leg : Hist_legal ini f_law s_law hist) : Prop :=
 ∀ t, (ht : t < hist.length) → (T : Turn_fst (t+1)) →  f_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (Hist_legal_rtake _ _ _ _ _ leg) = ⟨ hist.rget ⟨t,ht⟩ , (Hist_legal_rtake_fst _ _ _ _ _ T ht leg)⟩


def fStrat_wHist (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) (leg : Hist_legal ini f_law s_law hist) :=
  { f_strat : fStrategy ini f_law s_law // fStrat_staged ini f_law s_law f_strat hist leg}


def sStrat_staged (ini : α) (f_law s_law : α → List β → (β → Prop)) (s_strat : sStrategy ini f_law s_law) (hist : List β) (leg : Hist_legal ini f_law s_law hist) : Prop :=
 ∀ t, (ht : t < hist.length) → (T : Turn_snd (t+1)) →  s_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) (Hist_legal_rtake _ _ _ _ _ leg) = ⟨ hist.rget ⟨t,ht⟩ , (Hist_legal_rtake_snd _ _ _ _ _ T ht leg)⟩


def sStrat_wHist (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) (leg : Hist_legal ini f_law s_law hist) :=
  { s_strat : sStrategy ini f_law s_law // sStrat_staged ini f_law s_law s_strat hist leg}


def Game_World.is_fst_staged_win  {α β : Type _} (g : Game_World α β) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) : Prop :=
  ∃ ws : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg,
  ∀ snd_s : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg,
  ({g with fst_strat := ws.val, snd_strat := snd_s.val} : Game α β).fst_win

def Game_World.is_snd_staged_win  {α β : Type _} (g : Game_World α β) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) : Prop :=
  ∃ ws : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg,
  ∀ fst_s : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg,
  ({g with fst_strat := fst_s.val, snd_strat := ws.val} : Game α β).snd_win


inductive Game_World.has_staged_WL (g : Game_World α β) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) : Prop where
| wf (h : g.is_fst_staged_win hist leg)
| ws (h : g.is_snd_staged_win hist leg)

lemma fStrat_staged_empty (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) :
  fStrat_staged ini f_law s_law f_strat [] Hist_legal.nil := by
  intro _ no
  contradiction

lemma sStrat_staged_empty (ini : α) (f_law s_law : α → List β → (β → Prop)) (s_strat : sStrategy ini f_law s_law) :
  sStrat_staged ini f_law s_law s_strat [] Hist_legal.nil := by
  intro _ no
  contradiction

lemma Game_World.has_WL_iff_has_staged_WL_empty (g : Game_World α β) :
  g.has_WL ↔ g.has_staged_WL [] Hist_legal.nil :=
  by
  constructor
  · intro h
    cases' h with h h
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_staged_WL.wf
      use ⟨ws, fStrat_staged_empty g.init_game_state g.fst_legal g.snd_legal ws⟩
      intro s_strat
      exact ws_prop s_strat.val
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_staged_WL.ws
      use ⟨ws, sStrat_staged_empty g.init_game_state g.fst_legal g.snd_legal ws⟩
      intro s_strat
      exact ws_prop s_strat.val
  · intro h
    cases' h with h h
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_WL.wf
      use ws.val
      intro s_strat
      exact ws_prop ⟨s_strat, sStrat_staged_empty g.init_game_state g.fst_legal g.snd_legal s_strat⟩
    · obtain ⟨ws, ws_prop⟩ := h
      apply Game_World.has_WL.ws
      use ws.val
      intro s_strat
      exact ws_prop ⟨s_strat, fStrat_staged_empty g.init_game_state g.fst_legal g.snd_legal s_strat⟩


lemma Game_World.has_WL_helper (g : Game_World α β) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) :
  g.has_staged_WL hist leg → (¬ g.is_fst_staged_win hist leg) → g.is_snd_staged_win hist leg := by
  intro m c
  cases' m with m m
  · exfalso ; exact c m
  · exact m

lemma fStrat_staged_cons (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : f_law ini hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : fStrat_staged ini f_law s_law f_strat (act :: hist) (Hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg)) :
  fStrat_staged ini f_law s_law f_strat hist leg := by
  intro t tl tf
  specialize st t (by rw [List.length_cons] ; apply lt_trans tl ; apply Nat.lt_succ_self) tf
  convert st using 2
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt tl
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt tl
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt tl
  · rw [eq_comm]
    apply @List.rget_cons_eq_self _ hist act ⟨t,tl⟩


lemma sStrat_staged_cons (ini : α) (f_law s_law : α → List β → (β → Prop)) (s_strat : sStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : s_law ini hist act) (len : List.length hist = t) (T : Turn_snd (t+1))
  (st : sStrat_staged ini f_law s_law s_strat (act :: hist) (Hist_legal.cons hist act (by rw [Turn_snd_iff_not_fst] at T ; rw [len, if_neg T] ; exact al) leg)) :
  sStrat_staged ini f_law s_law s_strat hist leg := by
  intro t tl tf
  specialize st t (by rw [List.length_cons] ; apply lt_trans tl ; apply Nat.lt_succ_self) tf
  convert st using 2
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt tl
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt tl
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt tl
  · rw [eq_comm]
    apply @List.rget_cons_eq_self _ hist act ⟨t,tl⟩


lemma sStrat_staged_cons' (ini : α) (f_law s_law : α → List β → (β → Prop)) (s_strat : sStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : f_law ini hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : sStrat_staged ini f_law s_law s_strat hist leg) :
  sStrat_staged ini f_law s_law s_strat (act :: hist) (Hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg) := by
  intro t' t'l t'f
  have  t'l' : t' < hist.length := by
    apply lt_of_le_of_ne
    · rw [← Nat.lt_succ]
      rw [List.length_cons] at t'l
      exact t'l
    · intro con
      rw [con, len] at t'f
      contradiction -- beautiful
  specialize st t' t'l' t'f
  convert st using 2
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · apply @List.rget_cons_eq_self _ hist act ⟨t', t'l'⟩

lemma fStrat_staged_cons' (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : s_law ini hist act) (len : List.length hist = t) (T : Turn_snd (t+1))
  (st : fStrat_staged ini f_law s_law f_strat hist leg) :
  fStrat_staged ini f_law s_law f_strat (act :: hist) (Hist_legal.cons hist act (by rw [Turn_snd_iff_not_fst] at T ; rw [len, if_neg T] ; exact al) leg) := by
  intro t' t'l t'f
  have  t'l' : t' < hist.length := by
    apply lt_of_le_of_ne
    · rw [← Nat.lt_succ]
      rw [List.length_cons] at t'l
      exact t'l
    · intro con
      rw [con, len] at t'f
      contradiction -- beautiful
  specialize st t' t'l' t'f
  convert st using 2
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · apply @List.rget_cons_eq_self _ hist act ⟨t', t'l'⟩


lemma sStrat_staged_cons'' (ini : α) (f_law s_law : α → List β → (β → Prop)) (s_strat : sStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : f_law ini hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : sStrat_staged ini f_law s_law s_strat (act :: hist) (Hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg)) :
  sStrat_staged ini f_law s_law s_strat hist leg := by
  intro t' t'l t'f
  have  t'l' : t' < (act :: hist).length := by
    apply lt_of_le_of_ne
    · rw [← Nat.lt_succ]
      rw [List.length_cons]
      apply lt_trans t'l
      rw [Nat.lt_succ]
      apply Nat.le_succ
    · intro con
      rw [List.length_cons] at con
      rw [con] at t'l
      --contradiction -- not beautiful
      exfalso
      apply Nat.not_succ_lt_self t'l
  specialize st t' t'l' t'f
  convert st using 2
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l'
  · apply @List.rget_cons_eq_self _ hist act ⟨t', t'l'⟩

#exit

lemma Game_World.conditioning_step (g : Game_World α β) (hg : g.playable) (t : Nat)
  (main : ∀ hist : List β, (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) → hist.length = t+1 → g.has_staged_WL hist leg) :
  ∀ hist : List β, (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) → hist.length = t → g.has_staged_WL hist leg := by
  intro hist leg len
  by_cases T : Turn_fst (t+1)
  · by_cases q : ∃ f_act : β, ∃ (al : g.fst_legal g.init_game_state hist f_act), (g.is_fst_staged_win (f_act :: hist) (Hist_legal.cons hist f_act (by rw [len, if_pos T] ; exact al) leg))
    · obtain ⟨f_act, al, ws, ws_prop⟩ := q
      apply Game_World.has_staged_WL.wf
      set ws' : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg := ⟨ws.val , (fStrat_staged_cons _ _ _ _ _ _ leg al len T ws.prop)⟩ with ws'_def
      use ws'
      intro s_strat
      specialize ws_prop ⟨s_strat.val, by apply sStrat_staged_cons' _ _ _ _ _ _ leg al len T s_strat.prop⟩
      apply ws_prop
    · push_neg at q
      have main' : ∀ (f_act : β) (al : fst_legal g g.init_game_state hist f_act), g.is_snd_staged_win (f_act :: hist) (Hist_legal.cons hist f_act (by rw [len, if_pos T] ; exact al) leg) :=
        by
        intro f_act al
        have leg' := (Hist_legal.cons hist f_act (by rw [len, if_pos T] ; exact al) leg)
        specialize main (f_act :: hist) leg' (by rw [List.length_cons, len])
        specialize q f_act al
        exact g.has_WL_helper (f_act :: hist) leg' main q
      obtain ⟨f_act, al⟩ := (hg hist leg).1 (by rw [len] ; exact T)
      obtain ⟨ws, ws_prop⟩ := main' f_act al
      apply Game_World.has_staged_WL.ws

      sorry
  · sorry



#exit

-- # Zermelo

/-
- Show that has_WL is equivalent to have_WL on staged strats staged for empty hists
- Show that if one hasWL for all staged hist of length n+1, then also for n, via main Zermelo step
- Show that for staged hists of length greater the the bound of isWL_wBound, we have_WL (via some cohenrent end assumption)
-/

lemma Game_World.Zermelo (g : Game_World α β) (T : Nat) (hg_WLT : g.isWL_wBound T) :
  g.has_WL :=
  by
