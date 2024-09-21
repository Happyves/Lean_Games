/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Termination


def PosGame_trans [DecidableEq α] (hist : List α) : α → Fin 3 :=
  fun p => if  p ∈ hist
           then if Turn_fst (hist.indexOf p)
                then 1
                else 2
           else 0


open Classical

def Positional_Game_World [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : Game_World_wDraw (α → Fin 3) α where
     init_game_state := fun _ => 0
     fst_transition := fun _ hist act => PosGame_trans (act :: hist)
     snd_transition := fun _ hist act => PosGame_trans (act :: hist)
     fst_win_states := fun ini hist => (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ)
     snd_win_states := fun ini hist => (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ)
     draw_states := fun ini hist => ∀ p : α, (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0
     fst_legal := fun ini hist act =>
                    if State_from_history_neutral_wDraw ini -- for ↓ don't know why field names not accepted ... might be fixed when updating
                         (fun ini hist => (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ))
                         (fun ini hist => (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ))
                         (fun ini hist => ∀ p : α, (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0)
                         hist
                    then act ∉ hist
                    else True
     snd_legal := fun ini hist act =>
                    if State_from_history_neutral_wDraw ini -- for ↓ don't know why field names not accepted ... might be fixed when updating
                         (fun ini hist => (Turn_fst (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ))
                         (fun ini hist => (Turn_snd (hist.length + 1) ∧ ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ))
                         (fun ini hist => ∀ p : α, (State_from_history ini (fun _ hist act => PosGame_trans (act :: hist)) (fun _ hist act => PosGame_trans (act :: hist)) hist) p ≠ 0)
                         hist
                    then act ∉ hist
                    else True


lemma Positional_Game_World_mem_state [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (p : α) (hist : List α) (h : p ∈ hist) :
     (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition hist) p ≠ 0 :=
     by
     cases' hist with x _
     · contradiction
     · dsimp [State_from_history, Positional_Game_World]
       rw [ite_self]
       dsimp [PosGame_trans]
       rw [if_pos h]
       split_ifs
       all_goals {decide}



lemma Positional_Game_World_playable [Inhabited α] [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : (Positional_Game_World win_sets).playable :=
     by
     intro hist _
     constructor
     · intro _
       by_cases N : State_from_history_neutral_wDraw (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_win_states (Positional_Game_World win_sets).snd_win_states (Positional_Game_World win_sets).draw_states hist
       · dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         simp_rw [if_pos N]
         dsimp [State_from_history_neutral_wDraw] at N
         replace N := N.2.2
         push_neg at N
         obtain ⟨p,pp⟩ := N
         use p
         contrapose! pp
         apply Positional_Game_World_mem_state win_sets p hist pp
       · use default
         dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         rw [if_neg N]
         apply True.intro
     · intro _
       by_cases N : State_from_history_neutral_wDraw (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_win_states (Positional_Game_World win_sets).snd_win_states (Positional_Game_World win_sets).draw_states hist
       · dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         simp_rw [if_pos N]
         dsimp [State_from_history_neutral_wDraw] at N
         replace N := N.2.2
         push_neg at N
         obtain ⟨p,pp⟩ := N
         use p
         contrapose! pp
         apply Positional_Game_World_mem_state win_sets p hist pp
       · use default
         dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N -- required for ↓, hopefully fixed in future version
         rw [if_neg N]
         apply True.intro





lemma Positional_Game_World.decreasing_neutral [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α))
  (hist Hist : List α)  (su : hist <:+ Hist) :
  let g := Positional_Game_World win_sets
  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (Hist)) x = 0) Finset.univ
  ⊆ Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (hist)) x = 0) Finset.univ :=
  by
  intro g
  intro x
  simp_rw [Finset.mem_filter]
  rintro ⟨_,xdef⟩
  refine' ⟨Finset.mem_univ _, _ ⟩
  cases' Hist with y l
  · rw [ List.suffix_nil] at su
    rw [su]
    exact xdef
  · dsimp [State_from_history, Positional_Game_World] at xdef
    rw [ite_self] at xdef
    dsimp [PosGame_trans] at *
    split_ifs at xdef
    · contradiction
    · contradiction
    · rename_i main
      cases' hist with z L
      · dsimp [State_from_history, Positional_Game_World]
      · dsimp [State_from_history, Positional_Game_World]
        rw [ite_self]
        unfold PosGame_trans
        rw [if_neg (by contrapose! main ; exact List.mem_of_mem_suffix main su)]





lemma Positional_Game_World.strict_decreasing_neutral [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α))
  (hist : List α) (act : α) :
  let g := Positional_Game_World win_sets ;
  Hist_legal g.init_game_state g.fst_legal g.snd_legal (act :: hist) →
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states hist →
  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist)) x = 0) Finset.univ
  ⊂ Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (hist)) x = 0) Finset.univ :=
  by
  intro g leg N
  rw [Finset.ssubset_iff_of_subset (Positional_Game_World.decreasing_neutral win_sets hist (act :: hist) (List.suffix_cons act hist))]
  use act
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · cases' hist with x l
    · dsimp [State_from_history, Positional_Game_World]
    · dsimp [State_from_history, Positional_Game_World]
      rw [ite_self]
      dsimp [PosGame_trans]
      cases' leg
      rename_i now
      split_ifs at now
      · dsimp [g, Positional_Game_World] at now
        rw [if_pos (by convert N)] at now
        rw [if_neg now]
      · dsimp [g, Positional_Game_World] at now
        rw [if_pos (by convert N)] at now
        rw [if_neg now]
  · apply Positional_Game_World_mem_state
    exact List.Mem.head hist




#check 1

#check Game_World.state_on_turn

#check Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral

#check Finset.card_le_card

#check Finset.card_lt_card

lemma Positional_Game_World.draw_states_iff [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (hist : List α) :
  let g := Positional_Game_World win_sets
  (∀ p : α, (State_from_history g.init_game_state g.fst_transition g.snd_transition hist) p ≠ 0)
  ↔  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (hist)) x = 0) Finset.univ = ∅ :=
  by
  intro g
  simp_rw [Finset.filter_eq_empty_iff, Finset.mem_univ, true_imp_iff]



lemma Positional_Game_World.strict_decreasing_neutral_hists [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α)) :
  let g := Positional_Game_World win_sets ;
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ n,
  let H := (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat)
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states (H n) →
  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (H (n+1))) x = 0) Finset.univ
  ⊂ Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (H n)) x = 0) Finset.univ :=
  by
  intro g f_strat s_strat n H N
  have := (H (n+1)).prop.1
  by_cases T : Turn_fst (n+1)
  · dsimp [H, History_on_turn]
    rw [dif_pos T]
    dsimp [H, History_on_turn] at this
    rw [dif_pos T] at this
    apply Positional_Game_World.strict_decreasing_neutral win_sets _ _ this N
  · dsimp [H, History_on_turn]
    rw [dif_neg T]
    dsimp [H, History_on_turn] at this
    rw [dif_neg T] at this
    apply Positional_Game_World.strict_decreasing_neutral win_sets _ _ this N


lemma Positional_Game_World.terminates [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α))
  (win_sets_nontrivial : ∅ ∉ win_sets) :
  let g := Positional_Game_World win_sets ;
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∃ n, ¬ Game_World_wDraw.state_on_turn_neutral g f_strat s_strat (n+1) ∧
    ∀ m ≤ n, Game_World_wDraw.state_on_turn_neutral g f_strat s_strat m :=
  by
  intro g f_strat s_strat
  let N := {s | ∃ n,
      let H := (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat n)
      s = Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition H) x = 0) Finset.univ
      ∧ State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states H}
  have N_nonempty : Set.Nonempty N := by
    use Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat 0)) x = 0) Finset.univ
    use 0
    intro H
    constructor
    · rfl
    · dsimp [H, History_on_turn, State_from_history_neutral_wDraw, Positional_Game_World]
      constructor
      · intro con
        obtain ⟨oh,no,pe⟩ := con.2
        dsimp [State_from_history] at pe
        rw [Finset.filter_false_of_mem (fun _ _ => by decide), Finset.subset_empty] at pe
        rw [pe] at no
        exact win_sets_nontrivial no
      · constructor
        · intro con
          obtain ⟨oh,no,pe⟩ := con.2
          dsimp [State_from_history] at pe
          rw [Finset.filter_false_of_mem (fun _ _ => by decide), Finset.subset_empty] at pe
          rw [pe] at no
          exact win_sets_nontrivial no
        · intro con
          apply con Inhabited.default
          dsimp [State_from_history]
  obtain ⟨n,ndef,ne⟩ := WellFounded.min_mem Finset.isWellFounded_ssubset.wf N N_nonempty
  use n
  constructor
  · intro con
    rw [Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral] at con
    apply @WellFounded.not_lt_min _ _ Finset.isWellFounded_ssubset.wf N N_nonempty
        (Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat (n+1))) x = 0) Finset.univ)
        (by use n+1 ) --; intro H ; exact ⟨rfl, con⟩ )
    rw [ndef]
    apply Positional_Game_World.strict_decreasing_neutral_hists
    apply ne
  · intro m mln
    rw [Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral]






-- TODO : show that hists mini in terms of suffix ; show that wld states of positional get maintaind














#check instWellFoundedLTNatInstLTNat


#check Nat.lt_wfRel.wf
#check Finset.filter_eq_empty_iff

#check Finset.isWellFounded_ssubset.wf

-- follwo proof method of ↓
#exit

lemma preChomp_reaches_empty {height length : ℕ}
  (f_strat : fStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law)
  (s_strat : sStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law) :
  ∃ n, Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n+1)) = ∅ ∧
    ∀ m ≤ n, Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (m)) ≠ ∅ :=
  by
  let states := {s | ∃ n, s = Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)) ∧ s ≠ ∅}
  have lem : Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat 0).val ≠ ∅ :=
    by
    dsimp only [History_on_turn, Chomp_state, preChomp]
    rw [Finset.filter_true_of_mem]
    · rw [← Finset.nonempty_iff_ne_empty]
      use (length, height)
      apply Chomp_init_has_len_hei height length
    · intro _ _ _ no
      contradiction
  have states_nonempty : Set.Nonempty states := by
    use  Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat 0)
    use 0
    -- wow
    -- constructor
    -- · rfl
    -- · apply lem
  obtain ⟨n,ndef,ne⟩ := WellFounded.min_mem Finset.isWellFounded_ssubset.wf states states_nonempty
  use n
  constructor
  · by_contra con
    apply @WellFounded.not_lt_min _ _ Finset.isWellFounded_ssubset.wf states states_nonempty (Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n+1))) (by use n+1)
    rw [ndef]
    apply preChomp_state_ssub f_strat s_strat n
    rw [← ndef]
    exact ne
  · intro m mln
    contrapose ne
    rw [ndef, not_not, ← Finset.subset_empty]
    rw [not_not] at ne
    rw [← ne]
    apply Chomp_state_sub_of_hist_suffix
    apply History_on_turn_suffix (preChomp height length).toGame_World
    exact mln
