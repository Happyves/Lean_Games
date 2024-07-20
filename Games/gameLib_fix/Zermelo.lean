
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



variable {α β : Sort _} in -- inside leads to massive problems, fixed from 4.9 onwards
mutual -- Remeber to thank Arthur Adjedj
inductive History_good  (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) : List β → Prop where
| mk hist : Hist_legal ini f_law s_law (hist) → State_from_history_neutral ini f_trans s_trans f_wins s_wins hist →  auxExists ini f_law s_law f_trans s_trans f_wins s_wins hist  →  History_good ini f_law s_law f_trans s_trans f_wins s_wins hist

inductive auxExists (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) : List β  → Prop where
| intro hist  (next : β)  :  History_good ini f_law s_law f_trans s_trans f_wins s_wins (next :: hist)  → auxExists ini f_law s_law f_trans s_trans f_wins s_wins hist
end

noncomputable
def auxExists_choose (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop)
  (hist : List β) (main : auxExists ini f_law s_law f_trans s_trans f_wins s_wins hist) :=
  Classical.choice <| let ⟨_,x, px⟩ := main; ⟨(⟨x, px⟩ : {next // History_good ini f_law s_law f_trans s_trans f_wins s_wins (next :: hist) })⟩

def Game_World.history_good (g : Game_World α β) := History_good g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states

def Game_World.aux_exist (g : Game_World α β) := auxExists g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states

noncomputable
def Game_World.aux_exist_choose (g : Game_World α β) (hist : List β) (main : g.aux_exist hist) := auxExists_choose g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist main



def rec_fStrategy (ini : α) (f_law s_law : α → List β → (β → Prop)) : fStrategy ini f_law s_law :=
  fun (hist : List β)  (T : Turn_fst (hist.length+1)) (leg : Hist_legal ini f_law s_law hist) =>
    match hist with
    | [] => sorry
    | _ :: [] => False.elim (by contradiction)
    | s :: f :: rest => sorry


lemma Game_World.Zermelo (g : Game_World α β) :
  g.isWL → g.has_WL :=
  by
  intro h
  contrapose h
