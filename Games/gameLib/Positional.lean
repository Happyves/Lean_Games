/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.StateAPI
import Games.gameLib.Playability


/-
This file describes a class of games know as positional games.
Positional games are played on a finite set of elements, where each element
may be claimed (or "colored") by either player. There is a set of subsets
that are considered "winning sets". The first player to claim all all elements
of a winning set (≈ monochromatic winning set) wins the game.
An example of such a gam is Tic-tac-toe.

The main concepts of this file are:
- `Positional_Game_World` describes a `Game_World_wDraw` representing a positional game.
- `Positional_Game_World.terminates` shows that positional games always terminate.
-/


/-- The color of the tile corresponds to the turn it was selcted on-/
def PosGame_trans [DecidableEq α] (hist : List α) : α → Fin 3 :=
  fun p => if  p ∈ hist
           then if Turn_fst ((hist.reverse.indexOf p) + 1)
                then 1
                else 2
           else 0



/-- The first player wins if there is a winiing set colored entirely in `1`-/
def PosGame_win_fst [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (ini : α → Fin 3) (hist : List α) : Prop :=
  ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) hist) x = 1) Finset.univ

/-- The second player wins if there is a winiing set colored entirely in `2`-/
def PosGame_win_snd [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (ini : α → Fin 3) (hist : List α) : Prop :=
  ∃ w ∈ win_sets, w ⊆ Finset.filter (fun x => (State_from_history ini (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) hist) x = 2) Finset.univ




open Classical


/--
A positional game is played o a board represented by a finite type α.
We represent the players claiming tiles as follows: the state is `(s : α → Fin 3)`
where tile `t` is claimed by the frist player if `s t = 1`, by the second player if
`s t = 2`, and is unclaimed if `s t = 0`.

Winning states corresond to monochromatic winning sets.
The game is a draw if all tiles are colored (yet not winnig set is monochromatic).
At each turn, a move (a tile) is legal to play if it wasn't claimed (ie. isn't in the history),
and if all tiles are claimed (and the game is a draw), all moves are considered legal.
-/
def Positional_Game_World [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : Game_World_wDraw (α → Fin 3) α where
     init_game_state := fun _ => 0
     fst_transition := fun hist act => PosGame_trans (act :: hist)
     snd_transition := fun hist act => PosGame_trans (act :: hist)
     fst_win_states := fun hist => ∃ H, H <:+ hist ∧ PosGame_win_fst win_sets (fun _ => 0) H
     snd_win_states := fun hist => ∃ H, H <:+ hist ∧ PosGame_win_snd win_sets (fun _ => 0) H
     draw_states := fun hist => ¬ (∃ H, H <:+ hist ∧ PosGame_win_fst win_sets (fun _ => 0) H) ∧ ¬ (∃ H, H <:+ hist ∧ PosGame_win_snd win_sets (fun _ => 0) H)
        ∧ ∀ p : α, (State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) hist) p ≠ 0
     fst_legal := fun hist act =>
                    if State_from_history_neutral_wDraw (fun _  : α => (0 : Fin 3)) -- for ↓ don't know why field names not accepted ... might be fixed when updating
                         (fun hist => ∃ H, H <:+ hist ∧ PosGame_win_fst win_sets (fun _ => 0) H)
                         (fun hist => ∃ H, H <:+ hist ∧ PosGame_win_snd win_sets (fun _ => 0) H)
                         (fun hist =>  ¬ (∃ H, H <:+ hist ∧ PosGame_win_fst win_sets (fun _ => 0) H) ∧ ¬ (∃ H, H <:+ hist ∧ PosGame_win_snd win_sets (fun _ => 0) H) ∧ ∀ p : α, (State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) hist) p ≠ 0)
                         hist
                    then act ∉ hist
                    else True
     snd_legal := fun hist act =>
                    if State_from_history_neutral_wDraw (fun _ : α => (0 : Fin 3))
                         (fun hist => ∃ H, H <:+ hist ∧ PosGame_win_fst win_sets (fun _ => 0) H)
                         (fun hist => ∃ H, H <:+ hist ∧ PosGame_win_snd win_sets (fun _ => 0) H)
                         (fun hist =>  ¬ (∃ H, H <:+ hist ∧ PosGame_win_fst win_sets (fun _ => 0) H) ∧ ¬ (∃ H, H <:+ hist ∧ PosGame_win_snd win_sets (fun _ => 0) H) ∧ ∀ p : α, (State_from_history (fun _ => 0) (fun hist act => PosGame_trans (act :: hist)) (fun hist act => PosGame_trans (act :: hist)) hist) p ≠ 0)
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

lemma Positional_Game_World_mem_state' [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (p : α) (hist : List α)
  (h : (State_from_history (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_transition (Positional_Game_World win_sets).snd_transition hist) p ≠ 0) :
    p ∈ hist :=
    by
    cases' hist with x _
    · contradiction
    · dsimp [State_from_history, Positional_Game_World] at h
      rw [ite_self] at h
      dsimp [PosGame_trans] at h
      split_ifs at h
      · rename_i m _
        exact m
      · rename_i m _
        exact m
      · contradiction



lemma Positional_Game_World_playable [Inhabited α] [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : (Positional_Game_World win_sets).playable :=
     by
     intro hist _
     constructor
     · intro _
       by_cases N : State_from_history_neutral_wDraw (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_win_states (Positional_Game_World win_sets).snd_win_states (Positional_Game_World win_sets).draw_states hist
       · dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N
         simp_rw [if_pos N]
         dsimp [State_from_history_neutral_wDraw] at N
         have No1 := N.1
         have No2 := N.2.1
         replace N := N.2.2
         push_neg at N No1 No2
         specialize N No1 No2
         obtain ⟨p,pp⟩ := N
         use p
         contrapose! pp
         apply Positional_Game_World_mem_state win_sets p hist pp
       · use default
         dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N
         rw [if_neg N]
         apply True.intro
     · intro _
       by_cases N : State_from_history_neutral_wDraw (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_win_states (Positional_Game_World win_sets).snd_win_states (Positional_Game_World win_sets).draw_states hist
       · dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N
         simp_rw [if_pos N]
         dsimp [State_from_history_neutral_wDraw] at N
         have No1 := N.1
         have No2 := N.2.1
         replace N := N.2.2
         push_neg at N No1 No2
         specialize N No1 No2
         obtain ⟨p,pp⟩ := N
         use p
         contrapose! pp
         apply Positional_Game_World_mem_state win_sets p hist pp
       · use default
         dsimp [Positional_Game_World]
         dsimp [Positional_Game_World] at N
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
  g.hist_legal (act :: hist) →
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




lemma Positional_Game_World.draw_states_iff [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) (hist : List α) :
  let g := Positional_Game_World win_sets
  (∀ p : α, (State_from_history g.init_game_state g.fst_transition g.snd_transition hist) p ≠ 0)
  ↔  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (hist)) x = 0) Finset.univ = ∅ :=
  by
  intro g
  simp_rw [Finset.filter_eq_empty_iff, Finset.mem_univ, true_imp_iff]



lemma Positional_Game_World.strict_decreasing_neutral_hists [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α)) :
  let g := Positional_Game_World win_sets ;
  ∀ (f_strat : g.fStrategy), ∀ (s_strat : g.sStrategy),
  ∀ n,
  let H := (g.hist_on_turn f_strat s_strat)
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states (H n) →
  Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (H (n+1))) x = 0) Finset.univ
  ⊂ Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (H n)) x = 0) Finset.univ :=
  by
  intro g f_strat s_strat n H N
  have := (H (n+1)).prop.1
  by_cases T : Turn_fst (n+1)
  · dsimp [H, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn]
    rw [dif_pos T]
    dsimp [H, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at this
    rw [dif_pos T] at this
    apply Positional_Game_World.strict_decreasing_neutral win_sets _ _ this N
  · dsimp [H, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn]
    rw [dif_neg T]
    dsimp [H, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn] at this
    rw [dif_neg T] at this
    apply Positional_Game_World.strict_decreasing_neutral win_sets _ _ this N



lemma Positional_Game_World.fst_win_suffix [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α))
  (hist Hist : List α)  (su : hist <:+ Hist) :
  let g := Positional_Game_World win_sets ;
  g.fst_win_states hist → g.fst_win_states Hist :=
  by
  rintro g ⟨H,Hdef,X⟩
  dsimp [g, Positional_Game_World] at *
  use H
  refine' ⟨List.IsSuffix.trans Hdef su,_⟩
  exact X


lemma Positional_Game_World.snd_win_suffix [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α))
  (hist Hist : List α)  (su : hist <:+ Hist) :
  let g := Positional_Game_World win_sets ;
  g.snd_win_states hist → g.snd_win_states Hist :=
  by
  rintro g ⟨H,Hdef,X⟩
  dsimp [g, Positional_Game_World] at *
  use H
  refine' ⟨List.IsSuffix.trans Hdef su,_⟩
  exact X

lemma List.not_suffix_cons_nil {a : α} {l : List α} : ¬ (a :: l <:+ []) := by
  simp_all only [suffix_nil, not_false_eq_true]

lemma Positional_Game_World.draw_win_suffix [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α))
  (hist Hist : List α)  (su : hist <:+ Hist) :
  let g := Positional_Game_World win_sets ;
  g.draw_states hist → (g.draw_states Hist ∨ g.fst_win_states Hist ∨ g.snd_win_states Hist) :=
  by
  rintro g D
  dsimp [g, Positional_Game_World] at *
  by_cases Q1 : (∃ H, H <:+ Hist ∧ PosGame_win_fst win_sets (fun x => 0) H)
  · right ; left ; exact Q1
  · by_cases Q2 : (∃ H, H <:+ Hist ∧ PosGame_win_snd win_sets (fun x => 0) H)
    · right ; right ; exact Q2
    · left
      constructor
      · exact Q1
      · constructor
        · exact Q2
        · intro p
          replace D := D.2.2 p
          contrapose! D
          cases' hist with ah h
          · dsimp [State_from_history]
          · cases' Hist with aH H
            · exfalso
              exact List.not_suffix_cons_nil su
            · dsimp [State_from_history] at *
              rw [ite_self, PosGame_trans] at *
              split_ifs at D
              · contradiction
              · contradiction
              · rename_i main
                rw [if_neg (by contrapose! main ; apply List.mem_of_mem_suffix main su )]




lemma Positional_Game_World.neutral_of_suffix [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α))
  (hist Hist : List α)  (su : hist <:+ Hist) :
  let g := Positional_Game_World win_sets ;
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states Hist
  → State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states hist :=
  by
  rintro g ⟨Nf, Ns,Nd⟩
  constructor
  · contrapose! Nf
    apply Positional_Game_World.fst_win_suffix _ _ _ su Nf
  · constructor
    · contrapose! Ns
      apply Positional_Game_World.snd_win_suffix _ _ _ su Ns
    · contrapose! Nd
      cases' Positional_Game_World.draw_win_suffix _ _ _ su Nd with Q Q Q
      · exact Q
      · cases' Q with Q Q
        · apply False.elim (Nf Q)
        · apply False.elim (Ns Q)



lemma Positional_Game_World.terminates [DecidableEq α] [Fintype α] [Inhabited α] (win_sets : Finset (Finset α))
  (win_sets_nontrivial : ∅ ∉ win_sets) :
  let g := Positional_Game_World win_sets ;
  ∀ (f_strat : g.fStrategy), ∀ (s_strat : g.sStrategy),
  ∃ n, ¬ Game_World_wDraw.state_on_turn_neutral g f_strat s_strat (n+1) ∧
    ∀ m ≤ n, Game_World_wDraw.state_on_turn_neutral g f_strat s_strat m :=
  by
  intro g f_strat s_strat
  let N := {s | ∃ n,
      let H := (g.hist_on_turn f_strat s_strat n)
      s = Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition H) x = 0) Finset.univ
      ∧ State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states H}
  have N_nonempty : Set.Nonempty N := by
    use Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (g.hist_on_turn f_strat s_strat 0)) x = 0) Finset.univ
    use 0
    intro H
    constructor
    · rfl
    · dsimp [H, Game_World_wDraw.hist_on_turn, Game_World.hist_on_turn, State_from_history_neutral_wDraw, Positional_Game_World]
      constructor
      · intro con
        obtain ⟨H,Hdef,X⟩ := con
        rw [List.suffix_nil] at Hdef
        rw [Hdef] at X
        obtain ⟨oh,no,pe⟩ := X
        dsimp [State_from_history] at pe
        rw [Finset.filter_false_of_mem (fun _ _ => by decide), Finset.subset_empty] at pe
        rw [pe] at no
        exact win_sets_nontrivial no
      · constructor
        · intro con
          obtain ⟨H,Hdef,X⟩ := con
          rw [List.suffix_nil] at Hdef
          rw [Hdef] at X
          obtain ⟨oh,no,pe⟩ := X
          dsimp [State_from_history] at pe
          rw [Finset.filter_false_of_mem (fun _ _ => by decide), Finset.subset_empty] at pe
          rw [pe] at no
          exact win_sets_nontrivial no
        · intro con
          apply con.2.2 Inhabited.default
          dsimp [State_from_history]
  obtain ⟨n,ndef,ne⟩ := WellFounded.min_mem Finset.isWellFounded_ssubset.wf N N_nonempty
  use n
  constructor
  · intro con
    rw [Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral] at con
    apply @WellFounded.not_lt_min _ _ Finset.isWellFounded_ssubset.wf N N_nonempty
        (Finset.filter (fun x => (State_from_history g.init_game_state g.fst_transition g.snd_transition (g.hist_on_turn f_strat s_strat (n+1))) x = 0) Finset.univ)
        (by use n+1 )
    rw [ndef]
    apply Positional_Game_World.strict_decreasing_neutral_hists
    apply ne
  · intro m mln
    rw [Game_World_wDraw.state_on_turn_neutral_State_from_history_neutral]
    apply Positional_Game_World.neutral_of_suffix _ _ (g.hist_on_turn f_strat s_strat n).val
    · dsimp [Game_World_wDraw.hist_on_turn]
      apply Game_World.hist_on_turn_suffix
      exact mln
    · exact ne



lemma Positional_Game_World.col_fst_of_turn_fst [DecidableEq α] [Fintype α] [Inhabited α] {win_sets : Finset (Finset α)}
  (hist : List α) (act : α) (leg : (Positional_Game_World win_sets).hist_legal (act :: hist))
  (ts : Turn_fst (hist.length + 1)) :
  let g := (Positional_Game_World win_sets) ;
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states (hist) →
  (State_from_history g.init_game_state g.fst_transition  g.snd_transition (act :: hist)) act = 1 :=
  by
  intro g N
  dsimp [State_from_history]
  rw [if_pos ts]
  dsimp [Positional_Game_World, PosGame_trans]
  rw [if_pos (by apply List.mem_cons_self)]
  cases' leg
  rename_i _ now
  rw [if_pos ts] at now
  dsimp [Positional_Game_World] at now
  rw [if_pos (by  convert N), ← List.mem_reverse] at now
  rw [if_pos (by rw [List.reverse_cons, List.indexOf_append_of_not_mem now, List.length_reverse, List.indexOf_cons_eq _ rfl] ; exact ts)]






lemma Positional_Game_World.col_snd_of_turn_snd [DecidableEq α] [Fintype α] [Inhabited α] {win_sets : Finset (Finset α)}
  (hist : List α) (act : α) (leg : (Positional_Game_World win_sets).hist_legal (act :: hist))
  (ts : ¬ Turn_fst (hist.length + 1)) :
  let g := (Positional_Game_World win_sets) ;
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states (hist) →
  (State_from_history g.init_game_state g.fst_transition  g.snd_transition (act :: hist)) act = 2 :=
  by
  intro g N
  dsimp [State_from_history]
  rw [if_neg ts]
  dsimp [Positional_Game_World, PosGame_trans]
  rw [if_pos (by apply List.mem_cons_self)]
  cases' leg
  rename_i _ now
  rw [if_neg ts] at now
  dsimp [Positional_Game_World] at now
  rw [if_pos (by  convert N), ← List.mem_reverse] at now
  rw [if_neg (by rw [List.reverse_cons, List.indexOf_append_of_not_mem now, List.length_reverse, List.indexOf_cons_eq _ rfl] ; exact ts)]


lemma Positional_Game_World.turn_fst_of_col_fst [DecidableEq α] [Fintype α] [Inhabited α] {win_sets : Finset (Finset α)}
  (hist : List α) (act : α) (leg : (Positional_Game_World win_sets).hist_legal (act :: hist)) :
  let g := (Positional_Game_World win_sets) ;
  (State_from_history g.init_game_state g.fst_transition  g.snd_transition (act :: hist)) act = 1 →
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states (hist) →
  Turn_fst (hist.length + 1) :=
  by
  intro g S N
  by_contra con
  dsimp [State_from_history] at S
  rw [if_neg con] at S
  dsimp [Positional_Game_World, PosGame_trans] at S
  rw [if_pos (by apply List.mem_cons_self)] at S
  cases' leg
  rename_i _ now
  rw [if_neg con] at now
  dsimp [Positional_Game_World] at now
  rw [if_pos (by  convert N), ← List.mem_reverse] at now
  rw [if_neg (by rw [List.reverse_cons, List.indexOf_append_of_not_mem now, List.length_reverse, List.indexOf_cons_eq _ rfl] ; exact con)] at S
  contradiction



lemma Positional_Game_World.turn_snd_of_col_snd [DecidableEq α] [Fintype α] [Inhabited α] {win_sets : Finset (Finset α)}
  (hist : List α) (act : α) (leg : (Positional_Game_World win_sets).hist_legal (act :: hist)) :
  let g := (Positional_Game_World win_sets) ;
  (State_from_history g.init_game_state g.fst_transition  g.snd_transition (act :: hist)) act = 2 →
  State_from_history_neutral_wDraw g.init_game_state g.fst_win_states g.snd_win_states g.draw_states (hist) →
  ¬ Turn_fst (hist.length + 1) :=
  by
  intro g S N con
  dsimp [State_from_history] at S
  rw [if_pos con] at S
  dsimp [Positional_Game_World, PosGame_trans] at S
  rw [if_pos (by apply List.mem_cons_self)] at S
  cases' leg
  rename_i _ now
  rw [if_pos con] at now
  dsimp [Positional_Game_World] at now
  rw [if_pos (by  convert N), ← List.mem_reverse] at now
  rw [if_pos (by rw [List.reverse_cons, List.indexOf_append_of_not_mem now, List.length_reverse, List.indexOf_cons_eq _ rfl] ; exact con)] at S
  contradiction
