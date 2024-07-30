
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



#exit

def fStrat_staged (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_strat : fStrategy ini f_law s_law) (hist : List β) : Prop :=
 ∀ t, (ht : t < hist.length) → (T : Turn_fst (t+1)) → f_strat (hist.rtake t) (by rw [List.length_rtake (le_of_lt ht)] ; exact T) sorry = ⟨ hist.get ⟨t,ht⟩ , sorry⟩



def fStrat_wHist (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) :=
  { f_strat : fStrategy ini f_law s_law // fStrat_staged ini f_law s_law f_strat hist}


-- # Zermelo

/-
- Show that has_WL is equivalent to have_WL on staged strats staged for empty hists
- Show that if one hasWL for all staged hist of length n+1, then also for n, via main Zermelo step
- Show that for staged hists of length greater the the bound of isWL_wBound, we have_WL (via some cohenrent end assumption)
-/

lemma Game_World.Zermelo (g : Game_World α β) (T : Nat) (hg_WLT : g.isWL_wBound T) :
  g.has_WL :=
  by
