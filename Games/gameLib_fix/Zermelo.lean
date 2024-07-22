
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


def Game_World.playable (g : Game_World α β) : Prop := ∀ hist : List β, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist →
  --State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist →
  (Turn_fst (hist.length+1) → ∃ act : β, g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (hist.length+1) → ∃ act : β, g.snd_legal g.init_game_state hist act)


-- Assumes that the initial satte is neutral
inductive State_from_history_neutral_strong (ini : α) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) : List β → Prop where
| nil : State_from_history_neutral_strong ini f_trans s_trans f_wins s_wins []
| cons (act : β) (hist : List β) : State_from_history_neutral_strong ini f_trans s_trans f_wins s_wins hist →
    State_from_history_neutral ini f_trans s_trans f_wins s_wins (act :: hist) → State_from_history_neutral_strong ini f_trans s_trans f_wins s_wins (act :: hist)


open Classical

noncomputable
def damocles_fStrategy (g : Game_World α β) (hg : g.playable) : fStrategy g.init_game_state g.fst_legal g.snd_legal :=
  fun (hist : List β)  (T : Turn_fst (hist.length+1)) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) =>
  if N : ∃ act, g.fst_legal g.init_game_state hist act ∧ g.fst_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist))
  then ⟨Classical.choose N, (Classical.choose_spec N).1⟩
  else ⟨Classical.choose ((hg hist leg).1 T) , Classical.choose_spec ((hg hist leg).1 T)⟩

noncomputable
def damocles_sStrategy (g : Game_World α β) (hg : g.playable) : sStrategy g.init_game_state g.fst_legal g.snd_legal :=
  fun (hist : List β)  (T : Turn_snd (hist.length+1)) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) =>
  if N : ∃ act, g.snd_legal g.init_game_state hist act ∧ g.snd_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist))
  then ⟨Classical.choose N, (Classical.choose_spec N).1⟩
  else ⟨Classical.choose ((hg hist leg).2 T) , Classical.choose_spec ((hg hist leg).2 T)⟩


structure history_safe (g : Game_World α β) (hist : List β) : Prop where
  leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist
  neu : State_from_history_neutral_strong g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist
  prolong_fst : (Turn_fst (hist.length+1) → ∃ act : β, g.fst_legal g.init_game_state hist act ∧ (∀ next : β, g.snd_legal g.init_game_state (act :: hist) next → ¬ g.snd_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (next :: act :: hist))))
  prolong_snd : (Turn_snd (hist.length+1) → ∃ act : β, g.snd_legal g.init_game_state hist act ∧ (∀ next : β, g.fst_legal g.init_game_state (act :: hist) next → ¬ g.fst_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (next :: act :: hist))))

lemma main (g : Game_World α β) (hgp : g.playable) (hgw : ¬ g.has_WL) :
  ∃ chain : ℕ → β, ∀ t, history_safe g ((List.range t).map chain) :=
  by
  by_contra! con




-- lemma main (g : Game_World α β) (hgp : g.playable) (hgw : ¬ g.has_WL) :
--   ∃ hist : List β, History_good g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist
--   :=
--   by
--   by_contra! con
--   have : ∀ hist : List β,  Hist_legal g.init_game_state g.fst_legal g.snd_legal (hist) → State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist →
--          ∀ next : β, ¬ History_good g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states (next :: hist) :=
--     by
--     intro h leg neu next good
--     apply con h
--     exact ⟨h, leg, neu, ⟨h, next, good⟩⟩


def Game_World.isWL_alt (g : Game_World α β) : Prop :=
  ∀ hist : List β,  Hist_legal g.init_game_state g.fst_legal g.snd_legal (hist) →
    ∀ futures : Nat → List β, (∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal ((futures t) ++ hist)) →
      (∀ t, (futures t) ≥ t) →



lemma Game_World.Zermelo (g : Game_World α β) :
  g.isWL → g.has_WL :=
  by
  intro h
  contrapose h
  replace h := g.not_has_WL h
  dsimp [is_fst_win, is_snd_win] at h
  push_neg at h
