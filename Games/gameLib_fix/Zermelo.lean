
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



variable {α β : Sort _} in -- inside leads to massive problems
mutual -- Remeber to thank Arthur Adjedj
inductive History_good  (ini : α) (f_law s_law : α → List β → (β → Prop)) : List β → β → Prop where
| mk hist act : Hist_legal ini f_law s_law (act :: hist) → auxExists ini f_law s_law hist act →  History_good ini f_law s_law hist act

inductive auxExists (ini : α) (f_law s_law : α → List β → (β → Prop)) : List β → β → Prop where
| intro hist act (next : β)  :  History_good ini f_law s_law (act :: hist) next → auxExists ini f_law s_law hist act
end


lemma Game_World.Zermelo (g : Game_World α β) :
  g.isWL → g.has_WL :=
  by
  sorry
  -- intro h
  -- contrapose h
  -- unfold Game_World.isWL
  -- push_neg
