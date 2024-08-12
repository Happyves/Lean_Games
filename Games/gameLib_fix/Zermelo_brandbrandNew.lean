
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


lemma List.rget_cons_length {l : List α} {x : α} : (x :: l).rget ⟨l.length, (by rw [List.length_cons] ; exact Nat.le.refl)⟩ = x := by
  unfold List.rget
  dsimp
  simp_rw [Nat.succ_sub_one, Nat.sub_self]
  apply List.get_cons_zero

lemma List.rtake_length {l : List α}  : l.rtake l.length = l := by
  unfold List.rtake ; rw [Nat.sub_self] ; apply List.drop_zero




lemma List.rtake_all_of_le {α : Type _} {n : ℕ} {l : List α} (h : List.length l ≤ n) : l.rtake n  = l := by
  unfold List.rtake ; rw [Nat.sub_eq_zero_of_le h]  ; apply List.drop_zero

lemma List.length_le_of_suffix (m : l <:+ L) : l.length ≤ L.length := by
  rw [List.suffix_iff_eq_append] at m
  rw [← m, List.length_append]
  exact Nat.le_add_left (length l) (length (take (length L - length l) L))




lemma List.rget_suffix {α : Type _} {l L : List α} (m : l <:+ L) (n : Fin l.length) : L.rget ⟨n.val, by apply lt_of_lt_of_le n.prop (List.length_le_of_suffix m)⟩ = l.rget n := by
  rw [List.suffix_iff_eq_append] at m
  have : (take (length L - length l) L ++ l).rget { val := ↑n, isLt := by rw [m] ; rw [← List.suffix_iff_eq_append] at m ; apply lt_of_lt_of_le n.prop (List.length_le_of_suffix m) } = rget l n := by
    unfold List.rget
    rw [List.get_append_right]
    · dsimp
      congr 2
      simp_rw [List.length_append]
      cases' l with x l
      · have := n.prop
        contradiction
      · rw [Nat.add_sub_assoc (by rw [List.length_cons] ; linarith)]
        rw [Nat.add_sub_assoc (by rw [← Nat.pred_eq_sub_one] ; apply Nat.le_pred_of_lt ; exact n.prop )]
        rw [Nat.add_sub_cancel_left]
    · dsimp
      simp_rw [List.length_append, not_lt]
      cases' l with x l
      · have := n.prop
        contradiction
      · rw [Nat.add_sub_assoc (by rw [List.length_cons] ; linarith)]
        rw [Nat.add_sub_assoc (by rw [← Nat.pred_eq_sub_one] ; apply Nat.le_pred_of_lt ; exact n.prop )]
        exact Nat.le_add_right (length (take (length L - length (x :: l)) L)) (length (x :: l) - 1 - ↑n)
    · dsimp
      simp_rw [List.length_append]
      cases' l with x l
      · have := n.prop
        contradiction
      · rw [Nat.add_sub_assoc (by rw [List.length_cons] ; linarith)]
        rw [Nat.add_sub_assoc (by rw [← Nat.pred_eq_sub_one] ; apply Nat.le_pred_of_lt ; exact n.prop )]
        rw [Nat.add_sub_cancel_left]
        rw [Nat.sub_sub]
        apply Nat.sub_lt
        · rw [List.length_cons] ; linarith
        · rw [add_comm]
          apply Nat.zero_lt_succ
  convert this
  rw [m]



lemma List.rtake_suffix_comm (M : List.rtake hist (List.length h) <:+ h) (L : List.length hist ≤ List.length h) : hist = List.rtake h (List.length hist) := by
  rw [List.rtake_all_of_le L] at M
  induction' hist with x l ih
  · dsimp ; rw [List.rtake_zero]
  · rw [List.length_cons]
    have : length l < length h := by apply lt_of_lt_of_le _ L ; rw [List.length_cons] ; apply Nat.lt_succ_self
    rw [@List.rget_cons_rtake _ _ ⟨l.length, this ⟩]
    congr
    · rw [eq_comm]
      rw [List.rget_suffix M ⟨l.length, by rw [List.length_cons] ; linarith⟩ ]
      apply List.rget_cons_length
    · apply ih _ (le_of_lt this)
      apply IsSuffix.trans _ M
      exact suffix_cons x l







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



noncomputable
def exStrat_staged_fst [DecidableEq β] (g : Game_World α β) (hg : g.playable) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg :=
   ⟨fun h ht hl =>
      if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      then ⟨hist.rget ⟨h.length, M.2⟩, (by convert Hist_legal_rtake_fst g.init_game_state g.fst_legal g.snd_legal hist h.length ht M.2 leg ; exact M.1)⟩
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


noncomputable
def exStrat_staged_snd [DecidableEq β] (g : Game_World α β) (hg : g.playable) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg :=
   ⟨fun h ht hl =>
      if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      then ⟨hist.rget ⟨h.length, M.2⟩, (by convert Hist_legal_rtake_snd g.init_game_state g.fst_legal g.snd_legal hist h.length ht M.2 leg ; exact M.1)⟩
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

lemma fStrat_staged_cons''' (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : s_law ini hist act) (len : List.length hist = t) (T : Turn_snd (t+1))
  (st : fStrat_staged ini f_law s_law f_strat (act :: hist) (Hist_legal.cons hist act (by rw [Turn_snd_iff_not_fst] at T ; rw [len, if_neg T] ; exact al) leg)) :
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
    exact le_of_lt t'l
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l
  · rw [eq_comm]
    apply @List.rget_cons_eq_self _ hist act ⟨t', t'l⟩


lemma fStrat_staged_cons'' (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (act : β) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (al : f_law ini hist act) (len : List.length hist = t) (T : Turn_fst (t+1))
  (st : fStrat_staged ini f_law s_law f_strat (act :: hist) (Hist_legal.cons hist act (by rw [len, if_pos T] ; exact al) leg)) :
  fStrat_staged ini f_law s_law f_strat hist leg := by
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
    exact le_of_lt t'l
  · rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l
  · funext _
    rw [List.rtake_cons_eq_self]
    exact le_of_lt t'l
  · rw [eq_comm]
    apply @List.rget_cons_eq_self _ hist act ⟨t', t'l⟩



lemma Game_World.History_of_staged_length (g : Game_World α β) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist)
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) (s_strat : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) :
  (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val s_strat.val hist.length).val = hist := by
  induction' hist with x l ih
  · rfl
  · cases' leg
    rename_i sofar now
    dsimp [History_on_turn]
    split_ifs with T
    · rw [if_pos T] at now
      dsimp
      have main : ↑(History_on_turn g.init_game_state g.fst_legal g.snd_legal (f_strat.val) (s_strat.val) (List.length l)) = l := ih sofar ⟨f_strat.val, fStrat_staged_cons'' _ _ _ _ _ _ sofar now rfl T f_strat.prop⟩ ⟨s_strat.val, sStrat_staged_cons'' _ _ _ _ _ _ sofar now rfl T s_strat.prop⟩
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
        · dsimp
          unfold List.rget
          dsimp!
          simp_rw [Nat.succ_sub_one, Nat.sub_self]
          rfl
      --· apply main -- congr magic
    · rw [if_neg T] at now
      rw [← Turn_snd_iff_not_fst] at T
      dsimp
      have main : ↑(History_on_turn g.init_game_state g.fst_legal g.snd_legal (f_strat.val) (s_strat.val) (List.length l)) = l := ih sofar ⟨f_strat.val, fStrat_staged_cons''' _ _ _ _ _ _ sofar now rfl T f_strat.prop⟩ ⟨s_strat.val, sStrat_staged_cons _ _ _ _ _ _ sofar now rfl T s_strat.prop⟩
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

lemma Game_World.History_of_staged_rtake (g : Game_World α β) (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist)
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) (s_strat : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg)
  (n : Nat) (nbnd : n < hist.length) :
  (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val s_strat.val n).val = hist.rtake n := by
  induction' hist with x l ih
  · dsimp at nbnd
    contradiction
  · rw [List.rtake_cons_eq_self (by rw [List.length_cons, Nat.lt_succ] at nbnd ; exact nbnd)]
    cases' leg
    rename_i sofar now
    have st_1 : fStrat_staged g.init_game_state g.fst_legal g.snd_legal (f_strat.val) l sofar := by
      split_ifs at now with T
      · apply fStrat_staged_cons'' _ _ _ _ x l sofar now rfl T f_strat.prop
      · rw [Turn_not_fst_iff_snd] at T
        apply fStrat_staged_cons''' _ _ _ _ x l sofar now rfl T f_strat.prop
    have st_2 : sStrat_staged g.init_game_state g.fst_legal g.snd_legal (s_strat.val) l sofar := by
      split_ifs at now with T
      · apply sStrat_staged_cons'' _ _ _ _ x l sofar now rfl T s_strat.prop
      · rw [Turn_not_fst_iff_snd] at T
        apply sStrat_staged_cons _ _ _ _ x l sofar now rfl T s_strat.prop
    by_cases q : n < List.length l
    · exact ih sofar ⟨f_strat.val, st_1⟩ ⟨s_strat.val, st_2⟩ q
    · replace q : n = l.length := by apply Nat.eq_of_le_of_lt_succ (not_lt.mp q) nbnd
      rw [q, List.rtake_length]
      have := g.History_of_staged_length l sofar ⟨f_strat.val, st_1⟩ ⟨s_strat.val, st_2⟩
      convert this



open Classical

noncomputable
def sStrat_winner [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) (T : Turn_fst (List.length hist +1))
  (main : ∀ (f_act : β) (al : g.fst_legal g.init_game_state hist f_act), g.is_snd_staged_win (f_act :: hist) (Hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg)) :
  sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg :=
  ⟨fun h ht hl =>
      --if M : (h = (hist.rtake h.length)) ∧ (h.length < hist.length)
      if M : ((hist.rtake h.length) <:+ h)
      then
        if L : (h.length < hist.length)
        then ⟨hist.rget ⟨h.length, L⟩, (by convert Hist_legal_rtake_snd g.init_game_state g.fst_legal g.snd_legal hist h.length ht L leg ; rw [eq_comm] ; apply List.eq_of_suffix_of_length_eq M ; rw [List.length_rtake (le_of_lt L)])⟩
        else
          let f_act := h.rget ⟨hist.length, (by apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T ht)⟩
          have f_act_leg : g.fst_legal g.init_game_state hist f_act := by
            convert Hist_legal_rtake_fst g.init_game_state g.fst_legal g.snd_legal h hist.length T _ hl
            · rw [not_lt] at L
              apply List.rtake_suffix_comm M L
            · apply lt_of_le_of_ne (not_lt.mp L) ; intro con ; rw [con , Turn_fst_iff_not_snd] at T ; exact T ht
          (Classical.choose (main f_act f_act_leg)).val h ht hl
      else ⟨Classical.choose ((hg h hl).2 ht), Classical.choose_spec ((hg h hl).2 ht)⟩
  --       if W : (∃ f_act : β, (g.fst_legal g.init_game_state hist f_act) ∧ f_act :: hist <+: h)
  --       then
  --         let f_act := Classical.choose W
  --         let al := (Classical.choose_spec W).1
  --         --let sub := (Classical.choose_spec W).2
  --         let ws := Classical.choose (main f_act al)
  --         ws.val h ht hl
  --       else ⟨Classical.choose ((hg h hl).2 ht), Classical.choose_spec ((hg h hl).2 ht)⟩
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





lemma fStrat_staged_cons_f_act (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (hist : List β)
  (leg : Hist_legal ini f_law s_law (hist)) (T : Turn_fst (List.length hist + 1))
  (st : fStrat_staged ini f_law s_law f_strat hist leg) :
  let f_act := f_strat hist T leg ;
  fStrat_staged ini f_law s_law f_strat (f_act.val :: hist) (Hist_legal.cons hist f_act.val (by rw [if_pos T] ; exact f_act.prop) leg) := by
  intro f_act t' t'l t'f
  by_cases t'l' : t' < hist.length
  · specialize st t' t'l' t'f
    convert st using 2
    · funext _
      rw [List.rtake_cons_eq_self]
      exact le_of_lt t'l'
    · rw [List.rtake_cons_eq_self]
      exact le_of_lt t'l'
    · funext _
      rw [List.rtake_cons_eq_self]
      exact le_of_lt t'l'
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



-- ↓ to Basic
lemma fStrat_eq_of_hist_eq (ini : α) (f_law s_law : α → List β → β → Prop) (fs : fStrategy ini f_law s_law)
  (h H : List β) (hh : Hist_legal ini f_law s_law h) (hH : Hist_legal ini f_law s_law H) (Th : Turn_fst (h.length + 1)) (TH : Turn_fst (H.length + 1))
  (main : h = H) : (fs h Th hh ).val = (fs H TH hH).val :=
  by
  congr
  · rw [main]
  · apply heq_prop
  · apply heq_prop

lemma sStrat_eq_of_hist_eq (ini : α) (f_law s_law : α → List β → β → Prop) (fs : sStrategy ini f_law s_law)
  (h H : List β) (hh : Hist_legal ini f_law s_law h) (hH : Hist_legal ini f_law s_law H) (Th : Turn_snd (h.length + 1)) (TH : Turn_snd (H.length + 1))
  (main : h = H) : (fs h Th hh ).val = (fs H TH hH).val :=
  by
  congr
  · rw [main]
  · apply heq_prop
  · apply heq_prop


lemma oddly_specific (g : Game_World α β) (act : β) (hist : List β)
  (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal (hist)) (al : g.fst_legal g.init_game_state hist act) (T : Turn_fst (List.length hist + 1))
  (s_strat : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) (snd_s : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal (act :: hist) (Hist_legal.cons hist act (by rw [if_pos T] ; exact al) leg))
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) (n : Nat) (tu : Turn_snd (n+1))
  (main : let h := History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val s_strat.val n
          let H := History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val snd_s.val n
      n ≥ hist.length → (s_strat.val h.val (by rw [h.prop.2] ; exact tu) h.prop.1).val = (snd_s.val H.val (by rw [H.prop.2] ; exact tu)  H.prop.1).val ) :
  let h := History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val s_strat.val n
  let H := History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val snd_s.val n
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
    · rw [List.rtake_cons_eq_self (le_of_lt q)]
      rw [g.History_of_staged_rtake hist leg _ ⟨snd_s.val, sStrat_staged_cons'' _ _ _ _ act hist leg al rfl T snd_s.prop⟩ _ q]
    · rw [List.rtake_cons_eq_self (le_of_lt q)]
      rw [g.History_of_staged_rtake hist leg _ ⟨snd_s.val, sStrat_staged_cons'' _ _ _ _ act hist leg al rfl T snd_s.prop⟩ _ q]


lemma more_help (g : Game_World α β) (hist : List β)
  (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal (hist)) (T : Turn_fst (List.length hist + 1))
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) (s_strat : sStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg)
  (n : Nat) (tu : Turn_snd (n+1)) (n_bnd : n ≥ hist.length):
  let f_act := f_strat.val hist T leg
  (f_act.val :: hist) <+: History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat.val s_strat.val n :=
  by
  intro f_act
  revert tu n_bnd
  apply @Nat.twoStepInduction (fun n =>
    Turn_snd (n + 1) →
      n ≥ List.length hist →
        ↑f_act :: hist <+: ↑(History_on_turn g.init_game_state g.fst_legal g.snd_legal (f_strat.val) (s_strat.val) n))
  · intro no
    contradiction
  · intro _ L
    rw [ge_iff_le, Nat.le_one_iff_eq_zero_or_eq_one] at L
    cases' L with L L
    · rw [List.length_eq_zero] at L
      simp_rw [L, History_on_turn, dif_pos (show Turn_fst (0 + 1) from (by decide))]
      convert (List.prefix_refl [(f_strat.val hist T leg).val])
      · exact L.symm
      · exact L.symm
    · rw [L] at T
      contradiction
  · intro n ih1 ih2 tu n_bnd
    -- n_bnd not tight else contra with T and tu
    sorry

example {P Q : α → Prop} (a : ∃ p, P p) (b : ∃ q, Q q) (h : ∀ x, P x ↔ Q x) : Classical.choose a = Classical.choose b :=
  by congr ; funext x ; rw [h]

-- Probably stay in dtt hell for a week

#exit

lemma sStrat_winner_help_history [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal g.init_game_state hist f_act), g.is_snd_staged_win (f_act :: hist) (Hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.history_on_turn f_strat.val (sStrat_winner g hg hist leg T main).val = g.history_on_turn f_strat.val ws.val :=
  by
  intro f_act ws
  funext n
  induction' n with n ih
  · rfl
  · dsimp [Game_World.history_on_turn, History_on_turn]
    dsimp [Game_World.history_on_turn] at ih
    split_ifs with tu
    · apply Subtype.eq
      dsimp!
      congr 1
      · apply fStrat_eq_of_hist_eq
        rw [ih]
      · rw [ih]
    · rw [Turn_not_fst_iff_snd] at tu
      apply Subtype.eq
      dsimp!
      congr 1
      · apply oddly_specific g f_act.val hist leg f_act.prop T _ _ _ n tu
        intro h H n_bnd
        dsimp [sStrat_winner]
        rw [dif_pos]
        swap
        · simp_rw [History_on_turn_length]
          sorry
          -- rw [and_comm]
          -- push_neg
          -- intro no
          -- rw [History_on_turn_length] at no
          -- exfalso
          -- apply (not_lt_of_ge n_bnd) no
        · rw [dif_neg]
          swap
          · simp_rw [History_on_turn_length, not_lt]
            exact n_bnd
          · rw [ih]
          sorry
          --rw [dif_pos ⟨f_act.val, f_act.prop, more_help g hist leg T f_strat (sStrat_winner g hg hist leg T main) n tu n_bnd ⟩]
        -- show that eq follows from eq ≥ hist.length, as both are staged
        -- use ↑ to rw sStrat_winner with a first dif_neg
      · replace ih := congr_arg Subtype.val ih
        exact ih



#exit

lemma sStrat_winner_help_state [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal g.init_game_state hist f_act), g.is_snd_staged_win (f_act :: hist) (Hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) :
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  g.state_on_turn f_strat.val (sStrat_winner g hg hist leg T main).val = g.state_on_turn f_strat.val ws.val :=
  by
  intro f_act ws
  funext n
  cases' n with n
  · rfl
  · dsimp [Game_World.state_on_turn]
    split_ifs with tu
    · -- rw history thenrfl
      sorry
    · sorry

--#exit

lemma sStrat_winner_wins [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) (T : Turn_fst (List.length hist + 1))
  (main : ∀ (f_act : β) (al : g.fst_legal g.init_game_state hist f_act), g.is_snd_staged_win (f_act :: hist) (Hist_legal.cons hist f_act (by rw [if_pos T] ; exact al) leg))
  (f_strat : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal hist leg) :
  ({g with fst_strat := f_strat.val, snd_strat := (sStrat_winner g hg hist leg T main).val} : Game α β).snd_win :=
  by
  let f_act := f_strat.val hist T leg
  let ws := Classical.choose (main f_act.val f_act.prop)
  let ws_prop := Classical.choose_spec (main f_act.val f_act.prop)
  specialize ws_prop ⟨f_strat.val, (fStrat_staged_cons_f_act _ _ _ _ _ leg T f_strat.prop)⟩
  obtain ⟨τ, τw, τn⟩ := ws_prop
  dsimp at τw τn
  -- ↓ works!
  --rw [Game.state_on_turn, ← sStrat_winner_help_state] at τw

  -- conversion appraoch is doomed
  -- convert ws_prop using 2
  -- dsimp [sStrat_winner]
  -- funext h ht hl
  -- split_ifs with A B
  -- · sorry
  -- · sorry
  -- · sorry


#exit


-- # Hist from moves

def Hist_from_moves (moves : ℕ → β) : ℕ → List β := fun t => ((List.range t).reverse.map moves)

lemma Hist_from_moves_length (moves : ℕ → β) : ∀ t, (Hist_from_moves moves t).length = t := by
  intro t ; dsimp [Hist_from_moves] ; rw [List.length_map, List.length_reverse, List.length_range]

lemma Hist_from_moves_zero (moves : ℕ → β) : (Hist_from_moves moves 0) = [] := by
  rw [← List.length_eq_zero] ; apply Hist_from_moves_length


lemma Hist_from_moves_succ (moves : ℕ → β) : ∀ t, (Hist_from_moves moves (t+1)) = (moves (t)) :: (Hist_from_moves moves (t)):= by
  intro t ; dsimp [Hist_from_moves] ; rw [List.range_succ, List.reverse_append, List.map_append, List.reverse_singleton, List.map_singleton, List.singleton_append]


def moves_from_strats (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) :
  ℕ → β :=
  fun t =>
    let H := (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t)
    if T : Turn_fst (t+1) then (f_strat H.val (by rw [H.property.2] ; exact T) H.property.1).val else (s_strat H.val (by rw [Turn_snd_iff_not_fst, H.property.2] ; exact T) H.property.1).val

lemma moves_from_strats_history (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) :
  ∀ t, (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t).val = Hist_from_moves (moves_from_strats g f_strat s_strat) t :=
  by
  intro t
  induction' t with t ih
  · rfl
  · by_cases T : Turn_fst (t)
    · rw [History_on_turn_fst_to_snd _ _ _ _ _ t T]
      rw [Hist_from_moves_succ]
      unfold moves_from_strats
      rw [Turn_fst_not_step] at T
      rw [dif_neg T]
      congr
    · rw [History_on_turn_snd_to_fst _ _ _ _ _ t T]
      rw [Hist_from_moves_succ]
      unfold moves_from_strats
      rw [Turn_fst_not_step, not_not] at T
      rw [dif_pos T]
      congr


lemma moves_from_strats_legal (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) :
  ∀ t, (Turn_fst (t+1) → g.fst_legal g.init_game_state (Hist_from_moves (moves_from_strats g f_strat s_strat) t) ((moves_from_strats g f_strat s_strat) t))
    ∧ ( Turn_snd (t+1) → g.snd_legal g.init_game_state (Hist_from_moves (moves_from_strats g f_strat s_strat) t) ((moves_from_strats g f_strat s_strat) t)) :=
    by
    intro t
    constructor
    · intro T
      rw [← moves_from_strats_history g f_strat s_strat t]
      unfold moves_from_strats
      rw [dif_pos T]
      apply (f_strat ↑(History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t) _ _).property
    · intro T
      rw [← moves_from_strats_history g f_strat s_strat t]
      unfold moves_from_strats
      rw [dif_neg (by rw [Turn_not_fst_iff_snd] ; exact T)]
      apply (s_strat ↑(History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat t) _ _).property

lemma moves_from_strats_Hist_legal (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) :
  ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves (moves_from_strats g f_strat s_strat) t) :=
  by
  intro t
  induction' t with t ih
  · rw [Hist_from_moves_zero]
    apply Hist_legal.nil
  · rw [Hist_from_moves_succ]
    apply Hist_legal.cons _ _ _ ih
    rw [Hist_from_moves_length]
    split_ifs with T
    · apply (moves_from_strats_legal g f_strat s_strat t).1 T
    · apply (moves_from_strats_legal g f_strat s_strat t).2 T





lemma fStrategy_from_moves [DecidableEq β] (g : Game_World α β) (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) :
  fStrategy g.init_game_state g.fst_legal g.snd_legal :=
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


lemma sStrategy_from_moves [DecidableEq β] (g : Game_World α β) (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) :
  sStrategy g.init_game_state g.fst_legal g.snd_legal :=
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

lemma sStrategy_from_moves_eq  [DecidableEq β] (g : Game_World α β) (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t))
  (hist : List β) (T : Turn_snd (List.length hist + 1)) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) (M : hist = (Hist_from_moves moves (hist.length))) :
  sStrategy_from_moves g hg moves hm hist T leg = ⟨moves (hist.length),
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
  unfold sStrategy_from_moves
  rw [dif_pos M]


lemma fStrategy_from_moves_eq  [DecidableEq β] (g : Game_World α β) (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t))
  (hist : List β) (T : Turn_fst (List.length hist + 1)) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) (M : hist = (Hist_from_moves moves (hist.length))) :
  fStrategy_from_moves g hg moves hm hist T leg = ⟨moves (hist.length),
                      by
                      specialize hm (hist.length + 1)
                      rw [Hist_from_moves_succ] at hm
                      cases' hm
                      rename_i _ now
                      rw [← M, if_pos T] at now
                      exact now
                      ⟩ :=
  by
  unfold fStrategy_from_moves
  rw [dif_pos M]


lemma Hist_moves_strats [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (moves : ℕ → β) (leg : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) (t : Nat) :
  Hist_from_moves moves t = (History_on_turn g.init_game_state g.fst_legal g.snd_legal (fStrategy_from_moves g hg moves leg) (sStrategy_from_moves g hg moves leg) t).val :=
  by
  induction' t with t ih
  · rw [Hist_from_moves_zero]
    dsimp!
  · rw [Hist_from_moves_succ]
    by_cases q : Turn_fst (t)
    · rw [History_on_turn_fst_to_snd g.init_game_state g.fst_legal g.snd_legal (fStrategy_from_moves g hg moves leg) (sStrategy_from_moves g hg moves leg) t q]
      rw [ih]
      congr
      rw [sStrategy_from_moves_eq]
      · dsimp!
        rw [History_on_turn_length]
      · rw [History_on_turn_length]
        exact ih.symm
    · rw [Turn_not_fst_iff_snd] at q
      rw [History_on_turn_snd_to_fst g.init_game_state g.fst_legal g.snd_legal (fStrategy_from_moves g hg moves leg) (sStrategy_from_moves g hg moves leg) t q]
      rw [ih]
      congr
      rw [fStrategy_from_moves_eq]
      · dsimp!
        rw [History_on_turn_length]
      · rw [History_on_turn_length]
        exact ih.symm




lemma States_moves_strats [DecidableEq β] (g : Game_World α β) (hg : g.playable)
  (moves : ℕ → β) (leg : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) (T : Nat) :
  State_from_history g.init_game_state g.fst_transition g.snd_transition (Hist_from_moves moves T) =
  g.state_on_turn (fStrategy_from_moves g hg moves leg) (sStrategy_from_moves g hg moves leg) T := by
  cases' T with t
  · rw [Hist_from_moves_zero]
    dsimp!
  · rw [Hist_from_moves_succ]
    by_cases q : Turn_fst (t+1)
    · rw[g.state_on_turn_fst_to_snd _ _ _ q]
      dsimp [State_from_history]
      rw [Hist_from_moves_length, if_pos q]
      congr
      · dsimp [Game_World.history_on_turn]
        apply Hist_moves_strats
      · dsimp [Game_World.history_on_turn]
        rw [fStrategy_from_moves_eq]
        · dsimp!
          rw [History_on_turn_length]
        · rw [History_on_turn_length, eq_comm]
          apply Hist_moves_strats
    · rw[g.state_on_turn_snd_to_fst _ _ _ q]
      dsimp [State_from_history]
      rw [Hist_from_moves_length, if_neg q]
      congr
      · dsimp [Game_World.history_on_turn]
        apply Hist_moves_strats
      · dsimp [Game_World.history_on_turn]
        rw [sStrategy_from_moves_eq]
        · dsimp!
          rw [History_on_turn_length]
        · rw [History_on_turn_length, eq_comm]
          apply Hist_moves_strats



def Game_World.isWL_alt (g : Game_World α β) : Prop :=
  ∀ moves : ℕ → β, (∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) →
    ∃ T, (g.fst_win_states (State_from_history g.init_game_state  g.fst_transition g.snd_transition (Hist_from_moves moves T))) ∨ (g.snd_win_states (State_from_history g.init_game_state  g.fst_transition g.snd_transition (Hist_from_moves moves T)))


lemma Game_World.isWL_iff_isWL_alt [DecidableEq β] (g : Game_World α β) (hg : g.playable) : g.isWL ↔ g.isWL_alt :=
  by
  constructor
  · intro h moves leg
    specialize h (fStrategy_from_moves g hg moves leg) (sStrategy_from_moves g hg moves leg)
    obtain ⟨ T,Tp⟩ := h
    use T
    cases' Tp with TF TS
    · left
      convert TF
      apply States_moves_strats
    · right
      convert TS
      apply States_moves_strats
  · intro h f_strat s_strat
    specialize h (moves_from_strats g f_strat s_strat) (moves_from_strats_Hist_legal g f_strat s_strat)
    obtain ⟨T,q⟩ := h
    use T
    cases' q with F S
    · apply Turn_isWL.wf
      rw [← moves_from_strats_history g f_strat s_strat] at F
      rw [Game_World.state_on_turn_State_from_history]
      exact F
    · apply Turn_isWL.ws
      rw [← moves_from_strats_history g f_strat s_strat] at S
      rw [Game_World.state_on_turn_State_from_history]
      exact S


-- # experimental


noncomputable
def Y (r : α → α → Prop) (x : α) (h : ¬ Acc r x) : Nat → {y : α // ¬ Acc r y}
| 0 => ⟨x,h⟩
| n+1 =>
    let yn := (Y r x h n).val
    have N : ∃ next, r next yn ∧ (¬ Acc r next) := by
      have ynp := (Y r x h n).prop
      contrapose! ynp
      exact Acc.intro yn ynp
      done
    ⟨Classical.choose N, (Classical.choose_spec N).2⟩



lemma not_Acc (r : α → α → Prop) (x : α) (h : ¬ Acc r x) :
  ∃ Y : Nat → α, (Y 0 = x) ∧ (∀ n : Nat, r (Y (n+1)) (Y n)) :=
  by
  use (fun n => (Y r x h n).val)
  constructor
  · unfold Y
    rfl
  · intro n
    dsimp only [Y]
    apply (Classical.choose_spec (@Y.proof_3 α r x h (Nat.add n 0))).1


structure Rdef (g : Game_World α β) (h H : List β) : Prop where
  extend : ∃ a, H = a :: h
  neutral : State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states H
  leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal H

--#exit

def R  (g : Game_World α β) : List β → List β → Prop := fun H h =>  Rdef g h H

lemma Rdef_leg (g : Game_World α β) (h H : List β) (main : Rdef g h H) : Hist_legal g.init_game_state g.fst_legal g.snd_legal h :=
  by
  obtain ⟨a, m⟩ := main.extend
  replace main := main.leg
  rw [m] at main
  cases' main
  rename_i now sofar
  exact now

lemma Rdef_neutral (g : Game_World α β) (hgn : g.coherent_end) (h H : List β) (main : Rdef g h H) : State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states h :=
  by
  rw [State_from_history_neutral, ← not_or]
  intro con
  cases' con with con con
  · have := hgn.fst h (Rdef_leg g h H main) con
    obtain ⟨a,adef⟩ := main.extend
    have that := main.leg
    rw [adef] at that
    cases' that
    rename_i _ now
    split_ifs at now with T
    · replace this := (this a) ⟨fun _ => now, fun no => by exfalso ; rw [Turn_snd_iff_not_fst] at no ; exact no T⟩
      replace main := main.neutral
      rw [State_from_history_neutral, adef] at main
      exact main.1 this
    · replace this := (this a) ⟨fun no => by exfalso ; exact T no, fun _ => now⟩
      replace main := main.neutral
      rw [State_from_history_neutral, adef] at main
      exact main.1 this
  · have := hgn.snd h (Rdef_leg g h H main) con
    obtain ⟨a,adef⟩ := main.extend
    have that := main.leg
    rw [adef] at that
    cases' that
    rename_i _ now
    split_ifs at now with T
    · replace this := (this a) ⟨fun _ => now, fun no => by exfalso ; rw [Turn_snd_iff_not_fst] at no ; exact no T⟩
      replace main := main.neutral
      rw [State_from_history_neutral, adef] at main
      exact main.2 this
    · replace this := (this a) ⟨fun no => by exfalso ; exact T no, fun _ => now⟩
      replace main := main.neutral
      rw [State_from_history_neutral, adef] at main
      exact main.2 this




lemma wfR_hist_small [DecidableEq β] (h : List β)
  (Y : ℕ → List β) (Yne : ∀ (n : ℕ), Y (n + 1) ≠ []) :
  let moves : ℕ → β := fun n => if Q : n < List.length h then List.rget h { val := n, isLt := Q } else List.head (Y (n - List.length h + 1)) (Yne (n - List.length h))
  ∀ (t : ℕ), t < List.length h → (Hist_from_moves moves t) = h.rtake t :=
  by
  intro moves t tb
  induction' t with t ih
  · rw [Hist_from_moves_zero, List.rtake_zero]
  · rw [Hist_from_moves_succ]
    have : t < List.length h := lt_trans (Nat.lt_succ_self t) tb
    rw [@List.rget_cons_rtake _ _ ⟨t, this⟩, ih this]
    congr
    dsimp [moves]
    rw [dif_pos this]


lemma wfR_hist_big [DecidableEq β] (h : List β)
  (Y : ℕ → List β) (Y0 : Y 0 = h) (Yp : ∀ (n : ℕ), R g (Y (n + 1)) (Y n)) (Yne : ∀ (n : ℕ), Y (n + 1) ≠ []) :
  let moves : ℕ → β := fun n => if Q : n < List.length h then List.rget h { val := n, isLt := Q } else List.head (Y (n - List.length h + 1)) (Yne (n - List.length h))
  ∀ (t : ℕ), t ≥ List.length h → (Hist_from_moves moves t) = Y (t - List.length h) :=
  by
  intro moves t tb
  induction' t with t ih
  · simp_rw [Nat.le_zero, List.length_eq_zero] at tb
    simp_rw [tb] at *
    rw [Hist_from_moves_zero]
    dsimp
    exact Y0.symm
  · rw [Hist_from_moves_succ]
    by_cases q : t+1 > h.length
    · have : t ≥ h.length := by simp_rw [Nat.lt_succ] at q ; apply q
      rw [Nat.succ_sub this]
      obtain ⟨a, Yh⟩ := (Yp (t - h.length)).extend
      rw [Yh, ih this]
      congr
      dsimp [moves]
      rw [dif_neg (by rw [not_lt] ; apply this)]
      simp_rw [Yh, List.head_cons]
    · have := eq_of_ge_of_not_gt tb q
      have that : t < h.length := by rw [← this] ; apply (Nat.lt_succ_self t)
      rw [wfR_hist_small h Y Yne _ that]
      dsimp [moves]
      rw [dif_pos that, ← @List.rget_cons_rtake _ _ ⟨t, that⟩, this, Nat.sub_self, Y0]
      convert List.rtake_length



lemma wfR_legal [DecidableEq β] (g : Game_World α β) (h : List β)
  (Y : ℕ → List β) (Y0 : Y 0 = h) (Yp : ∀ (n : ℕ), R g (Y (n + 1)) (Y n)) (Yne : ∀ (n : ℕ), Y (n + 1) ≠ []) :
  let moves : ℕ → β := fun n => if Q : n < List.length h then List.rget h { val := n, isLt := Q } else List.head (Y (n - List.length h + 1)) (Yne (n - List.length h))
  ∀ (t : ℕ), Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t) :=
  by
  intro moves t
  by_cases q : t < List.length h
  · rw [wfR_hist_small h _ Yne _ q]
    apply Hist_legal_rtake
    apply Rdef_leg g _ (Y 1)
    specialize Yp 0
    rw [R, Y0] at Yp
    exact Yp
  · rw [not_lt] at q
    rw [wfR_hist_big h _ Y0 Yp Yne _ q]
    apply Rdef_leg g _ (Y ((t - List.length h) + 1))
    apply Yp (t - List.length h)



lemma wfR_hist_extend [DecidableEq β] (h : List β)
  (Y : ℕ → List β) (Y0 : Y 0 = h) (Yp : ∀ (n : ℕ), R g (Y (n + 1)) (Y n)) :
  ∀ (n : ℕ), ∃ f, Y n = f ++ h :=
  by
  intro n
  induction' n with n ih
  · use []
    rw [Y0, List.nil_append]
  · obtain ⟨a,adef⟩ := (Yp n).extend
    obtain ⟨f,fdef⟩ := ih
    use (a :: f)
    rw [adef,fdef, List.cons_append]


--#exit

lemma wfR [DecidableEq β] (g : Game_World α β) (hgw : g.isWL) (hgp : g.playable) (hgn : Game_World.coherent_end g) : WellFounded (R g) := by
  apply WellFounded.intro
  intro h
  by_contra con
  obtain ⟨Y, Y0,Yp⟩ := not_Acc _ h con
  rw [g.isWL_iff_isWL_alt hgp] at hgw
  have Yne : ∀ n, Y (n+1) ≠ [] := by
    intro n
    obtain ⟨a,yes⟩ := (Yp n).extend
    rw [yes]
    exact List.cons_ne_nil a (Y n)
  let moves (n : Nat) := if Q : n < h.length then h.rget ⟨n,Q⟩ else (Y ((n - h.length) + 1)).head (Yne (n - h.length))
  obtain ⟨T,Tdef⟩ := hgw moves (wfR_legal g h Y Y0 Yp Yne)
  by_cases qt : T < h.length
  · rw [wfR_hist_small h _ Yne _ qt] at Tdef
    rw [← List.rdrop_append_rtake T h] at Y0
    cases' Tdef with N N
    · apply (Rdef_neutral g hgn (Y 0) (Y (01)) (Yp (0))).1
      rw [Y0]
      apply g.coherent_end_all_fst hgn _ N
      rw [← Y0]
      apply Rdef_leg g _ (Y 1) (Yp 0)
    · apply (Rdef_neutral g hgn (Y 0) (Y (01)) (Yp (0))).2
      rw [Y0]
      apply g.coherent_end_all_snd hgn _ N
      rw [← Y0]
      apply Rdef_leg g _ (Y 1) (Yp 0)
  · rw [not_lt] at qt
    rw [wfR_hist_big h _ Y0 Yp Yne _ qt] at Tdef
    cases' Tdef with N N
    · exact (Rdef_neutral g hgn (Y (T - List.length h)) (Y (T - List.length h + 1)) (Yp (T - List.length h))).1 N
    · exact (Rdef_neutral g hgn (Y (T - List.length h)) (Y (T - List.length h + 1)) (Yp (T - List.length h))).2 N


lemma Game_World.staged_WL_of_win_state_fst (g : Game_World α β) (hgp : g.playable) (hgn : Game_World.coherent_end g)
  (h : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal h)
  (N : fst_win_states g (State_from_history g.init_game_state g.fst_transition g.snd_transition h)) :
  g.is_fst_staged_win h leg :=
  by
  use (exStrat_staged_fst g hgp h leg)
  intro s_strat
  apply Game.coherent_end_fst_win _ (by apply hgn)
  use h.length
  dsimp [Game.state_on_turn]
  rw [g.state_on_turn_State_from_history]
  convert N
  apply g.History_of_staged_length


lemma Game_World.staged_WL_of_win_state_snd (g : Game_World α β) (hgp : g.playable) (hgn : Game_World.coherent_end g)
  (h : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal h)
  (N : snd_win_states g (State_from_history g.init_game_state g.fst_transition g.snd_transition h)) :
  g.is_snd_staged_win h leg :=
  by
  use (exStrat_staged_snd g hgp h leg)
  intro s_strat
  apply Game.coherent_end_snd_win _ (by apply hgn)
  use h.length
  dsimp [Game.state_on_turn]
  rw [g.state_on_turn_State_from_history]
  convert N
  apply g.History_of_staged_length


lemma Game_World.staged_WL_of_win_state (g : Game_World α β) (hgp : g.playable) (hgn : Game_World.coherent_end g)
  (h : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal h)
  (N : fst_win_states g (State_from_history g.init_game_state g.fst_transition g.snd_transition h) ∨
  snd_win_states g (State_from_history g.init_game_state g.fst_transition g.snd_transition h)) :
  g.has_staged_WL h leg :=
  by
  cases' N with N N
  · apply Game_World.has_staged_WL.wf
    apply g.staged_WL_of_win_state_fst hgp hgn _ _ N
  · apply Game_World.has_staged_WL.ws
    apply g.staged_WL_of_win_state_snd hgp hgn _ _ N



lemma Game_World.conditioning_step [DecidableEq β] (g : Game_World α β) (hgw : g.isWL) (hgp : g.playable) (hgn : Game_World.coherent_end g)
  (hist : List β) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) :
  g.has_staged_WL hist leg :=
  by
  revert leg
  apply @WellFounded.induction _ _ (wfR g hgw hgp hgn) (fun x => ∀ (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal x),g.has_staged_WL x leg) hist
  intro h ih leg
  replace ih : ∀ (y : List β), (rel : R g y h) → has_staged_WL g y (rel.leg) := by
    intro y rel ; apply ih _ rel
  by_cases N : State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states h
  · by_cases T : Turn_fst (h.length+1)
    · by_cases q : ∃ f_act : β, ∃ (al : g.fst_legal g.init_game_state h f_act), (g.is_fst_staged_win (f_act :: h) (Hist_legal.cons h f_act (by rw [if_pos T] ; exact al) leg))
      · obtain ⟨f_act, al, ws, ws_prop⟩ := q
        apply Game_World.has_staged_WL.wf
        set ws' : fStrat_wHist g.init_game_state g.fst_legal g.snd_legal h leg := ⟨ws.val , (fStrat_staged_cons _ _ _ _ _ _ leg al rfl T ws.prop)⟩ with ws'_def
        use ws'
        intro s_strat
        specialize ws_prop ⟨s_strat.val, by apply sStrat_staged_cons' _ _ _ _ _ _ leg al rfl T s_strat.prop⟩
        apply ws_prop
      · push_neg at q
        have main' : ∀ (f_act : β) (al : fst_legal g g.init_game_state h f_act), g.is_snd_staged_win (f_act :: h) (Hist_legal.cons h f_act (by rw [if_pos T] ; exact al) leg) :=
          by
          intro f_act al
          have leg' := (Hist_legal.cons h f_act (by rw [if_pos T] ; exact al) leg)
          specialize ih (f_act :: h)
          specialize q f_act al
          by_cases Q : (State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states (f_act :: h))
          · exact g.has_WL_helper (f_act :: h) leg'
              (by
               apply ih
               constructor
               · use f_act
               · exact Q
               · exact leg'
              ) q
          · simp_rw [State_from_history_neutral, not_and_or, not_not] at Q
            cases' Q with Q Q
            · exfalso
              apply q
              apply g.staged_WL_of_win_state_fst hgp hgn _ _ Q
            · apply g.staged_WL_of_win_state_snd hgp hgn _ _ Q
        apply Game_World.has_staged_WL.ws
        use sStrat_winner g hgp h leg T main'
        intro f_strat
        sorry
    · sorry
  · unfold State_from_history_neutral at N
    simp_rw [not_and_or, not_not] at N
    apply g.staged_WL_of_win_state hgp hgn _ _ N



#exit

lemma Game_World.conditioning_step [DecidableEq β] (g : Game_World α β) (hg : g.playable) (t : Nat)
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
      apply Game_World.has_staged_WL.ws
      use sStrat_winner g hg hist leg len T main'
      intro f_strat
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
