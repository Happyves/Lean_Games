
import Games.gameLib_fix.Termination


lemma Game_World.not_has_WL (g : Game_World α β) (h : ¬ g.has_WL) :
  ¬ g.is_fst_win ∧ ¬ g.is_snd_win :=
  by
  contrapose h
  simp_rw [not_and_or, not_not] at h
  rw [not_not]
  cases' h with h h
  · exact Game_World.has_WL.wf h
  ·  exact Game_World.has_WL.ws h


inductive History_good : (α) → (α → List β → (β → Prop)) → (α → List β → (β → Prop)) → (List β) → (β) → Prop where
| mk (ini : α) (f_law s_law : α → List β → (β → Prop)) (hist : List β) (act : β) (leg : Hist_legal ini f_law s_law (act :: hist)) (good : ∃ next : β, History_good ini f_law s_law (act :: hist) next) : History_good ini f_law s_law hist act
  -- neutral : (State_of_hist act :: hist).neutral

--set_option trace.Elab.inductive true in
--set_option trace.Kernel true in
inductive test : Option Nat → Nat → Prop where
| mk (k) (n) (h : ∃ m, 1 = 0 →  test (k+1) m) : test (k) n

lemma Game_World.Zermelo (g : Game_World α β) :
  g.isWL → g.has_WL :=
  by
  intro h
  contrapose h
  unfold Game_World.isWL
  push_neg
