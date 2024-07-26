
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



-- variable {α β : Sort _} in -- inside leads to massive problems, fixed from 4.9 onwards
-- mutual -- Remeber to thank Arthur Adjedj
-- inductive History_good  (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) : List β → Prop where
-- | mk hist : Hist_legal ini f_law s_law (hist) → State_from_history_neutral ini f_trans s_trans f_wins s_wins hist →  auxExists ini f_law s_law f_trans s_trans f_wins s_wins hist  →  History_good ini f_law s_law f_trans s_trans f_wins s_wins hist

-- inductive auxExists (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) : List β  → Prop where
-- | intro hist  (next : β)  :  History_good ini f_law s_law f_trans s_trans f_wins s_wins (next :: hist)  → auxExists ini f_law s_law f_trans s_trans f_wins s_wins hist
-- end

-- noncomputable
-- def auxExists_choose (ini : α) (f_law s_law : α → List β → (β → Prop)) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop)
--   (hist : List β) (main : auxExists ini f_law s_law f_trans s_trans f_wins s_wins hist) :=
--   Classical.choice <| let ⟨_,x, px⟩ := main; ⟨(⟨x, px⟩ : {next // History_good ini f_law s_law f_trans s_trans f_wins s_wins (next :: hist) })⟩

-- def Game_World.history_good (g : Game_World α β) := History_good g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states

-- def Game_World.aux_exist (g : Game_World α β) := auxExists g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states

-- noncomputable
-- def Game_World.aux_exist_choose (g : Game_World α β) (hist : List β) (main : g.aux_exist hist) := auxExists_choose g.init_game_state g.fst_legal g.snd_legal g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist main


-- def Game_World.playable (g : Game_World α β) : Prop := ∀ hist : List β, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist →
--   --State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist →
--   (Turn_fst (hist.length+1) → ∃ act : β, g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (hist.length+1) → ∃ act : β, g.snd_legal g.init_game_state hist act)


-- -- Assumes that the initial satte is neutral
-- inductive State_from_history_neutral_strong (ini : α) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) : List β → Prop where
-- | nil : State_from_history_neutral_strong ini f_trans s_trans f_wins s_wins []
-- | cons (act : β) (hist : List β) : State_from_history_neutral_strong ini f_trans s_trans f_wins s_wins hist →
--     State_from_history_neutral ini f_trans s_trans f_wins s_wins (act :: hist) → State_from_history_neutral_strong ini f_trans s_trans f_wins s_wins (act :: hist)


-- open Classical

-- noncomputable
-- def damocles_fStrategy (g : Game_World α β) (hg : g.playable) : fStrategy g.init_game_state g.fst_legal g.snd_legal :=
--   fun (hist : List β)  (T : Turn_fst (hist.length+1)) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) =>
--   if N : ∃ act, g.fst_legal g.init_game_state hist act ∧ g.fst_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist))
--   then ⟨Classical.choose N, (Classical.choose_spec N).1⟩
--   else ⟨Classical.choose ((hg hist leg).1 T) , Classical.choose_spec ((hg hist leg).1 T)⟩

-- noncomputable
-- def damocles_sStrategy (g : Game_World α β) (hg : g.playable) : sStrategy g.init_game_state g.fst_legal g.snd_legal :=
--   fun (hist : List β)  (T : Turn_snd (hist.length+1)) (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) =>
--   if N : ∃ act, g.snd_legal g.init_game_state hist act ∧ g.snd_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist))
--   then ⟨Classical.choose N, (Classical.choose_spec N).1⟩
--   else ⟨Classical.choose ((hg hist leg).2 T) , Classical.choose_spec ((hg hist leg).2 T)⟩


-- structure history_safe (g : Game_World α β) (hist : List β) : Prop where
--   leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist
--   neu : State_from_history_neutral_strong g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states hist
--   prolong_fst : (Turn_fst (hist.length+1) → ∃ act : β, g.fst_legal g.init_game_state hist act ∧ (∀ next : β, g.snd_legal g.init_game_state (act :: hist) next → ¬ g.snd_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (next :: act :: hist))))
--   prolong_snd : (Turn_snd (hist.length+1) → ∃ act : β, g.snd_legal g.init_game_state hist act ∧ (∀ next : β, g.fst_legal g.init_game_state (act :: hist) next → ¬ g.fst_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition (next :: act :: hist))))


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


def Game_World.isWL_alt (g : Game_World α β) : Prop :=
  ∀ moves : ℕ → β, (∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) →
    ∃ T, (Turn_fst T ∧ g.fst_win_states (State_from_history g.init_game_state  g.fst_transition g.snd_transition (Hist_from_moves moves T))) ∨ (Turn_snd T ∧ g.snd_win_states (State_from_history g.init_game_state  g.fst_transition g.snd_transition (Hist_from_moves moves T)))

lemma fStrategy_from_moves [DecidableEq β] (g : Game_World α β) (hg : g.playable) (moves : ℕ → β) (hm : ∀ t, Hist_legal g.init_game_state g.fst_legal g.snd_legal (Hist_from_moves moves t)) :
  fStrategy g.init_game_state g.fst_legal g.snd_legal :=
  fun hist T leg => if hist = (Hist_from_moves moves (hist.length)) then ⟨moves (hist.length + 1), _ ⟩ else (g.exStrat_fst hg hist T leg)



#exit

lemma Game_World.isWL_iff_isWL_alt (g : Game_World α β) : g.isWL ↔ g.isWL_alt :=
  by
  constructor
  · intro h moves leg
    sorry
  · intro h f_strat s_strat
    specialize h (moves_from_strats g f_strat s_strat) (moves_from_strats_Hist_legal g f_strat s_strat)
    obtain ⟨T,q⟩ := h
    use T
    cases' q with F S
    · apply Turn_isWL.wf F.1
      rw [← moves_from_strats_history g f_strat s_strat] at F
      rw [Game_World.state_on_turn_State_from_history]
      exact F.2
    · apply Turn_isWL.ws S.1
      rw [← moves_from_strats_history g f_strat s_strat] at S
      rw [Game_World.state_on_turn_State_from_history]
      exact S.2

#exit

/-
Idea:

consider type of histories that are legal and neutral ; nonempty → empty hist ; disjoin on whether the length are bounded
or unbounded ; in the unbounded case show that the negation of the above `isWL_alt` holds ; in the bounded case, for a bound
T, show Zermelo by induction on T, as in the classic proof ?
Maybe look at histories rather then changing game-world. For a given hist, consider the set of hists that extend it and
reached a terminal state (there must be one such extention, by the case we're in)....
For inclusion maximal histories, next move must be terminating
-/


variable {α β : Sort _} in -- inside leads to massive problems, fixed from 4.9 onwards
mutual  -- Remeber to thank Arthur Adjedj

inductive Hist_good_fst (g : Game_World α β) : List β → Prop where
| ofWin (hist : List β) : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → Turn_fst (hist.length + 1) → g.fst_win_states (State_from_history g.init_game_state  g.fst_transition g.snd_transition hist) → Hist_good_fst g hist
| ofFst (hist : List β) : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → Turn_fst (hist.length + 1) → auxExists_fst g hist → Hist_good_fst g hist
| ofSnd (hist : List β) : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → Turn_snd (hist.length + 1) → (∀ next : β, g.snd_legal g.init_game_state hist next →  Hist_good_fst g (next :: hist)) → Hist_good_fst g hist


inductive auxExists_fst (g : Game_World α β) : List β → Prop where
| intro (hist : List β) : (next : β) → g.fst_legal g.init_game_state hist next → Hist_good_fst g (next :: hist) → auxExists_fst g hist
end


variable {α β : Sort _} in -- inside leads to massive problems, fixed from 4.9 onwards
mutual  -- Remeber to thank Arthur Adjedj

inductive Hist_good_snd (g : Game_World α β) : List β → Prop where
| ofWin (hist : List β) : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → Turn_snd (hist.length + 1) → g.fst_win_states (State_from_history g.init_game_state  g.fst_transition g.snd_transition hist) → Hist_good_snd g hist
| ofSnd (hist : List β) : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → Turn_snd (hist.length + 1) → auxExists_snd g hist → Hist_good_snd g hist
| ofFst (hist : List β) : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → Turn_fst (hist.length + 1) → (∀ next : β, g.fst_legal g.init_game_state hist next →  Hist_good_snd g (next :: hist)) → Hist_good_snd g hist


inductive auxExists_snd (g : Game_World α β) : List β → Prop where
| intro (hist : List β) : (next : β) → g.snd_legal g.init_game_state hist next → Hist_good_snd g (next :: hist) → auxExists_snd g hist
end


noncomputable
def auxExists_fst_choose (g : Game_World α β) (hist : List β) (main : auxExists_fst (g : Game_World α β) hist) :=
  Classical.choice <| let ⟨_,x, xl,xg⟩ := main; ⟨(⟨x, ⟨xl,xg⟩⟩ : {next // g.fst_legal g.init_game_state hist next ∧ Hist_good_fst g (next :: hist) })⟩

noncomputable
def auxExists_snd_choose (g : Game_World α β) (hist : List β) (main : auxExists_snd (g : Game_World α β) hist) :=
  Classical.choice <| let ⟨_,x, xl,xg⟩ := main; ⟨(⟨x, ⟨xl,xg⟩⟩ : {next // g.snd_legal g.init_game_state hist next ∧ Hist_good_snd g (next :: hist) })⟩




#exit

lemma Game_World.Zermelo (g : Game_World α β) :
  g.isWL → g.has_WL :=
  by
  intro h
  contrapose h
  replace h := g.not_has_WL h
  dsimp [is_fst_win, is_snd_win] at h
  push_neg at h
