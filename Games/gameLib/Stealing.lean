/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Games.gameLib.Zermelo


/-
This file contains API for a variant of an argument known as "strategy stealing".
It is used in the game of Chomp for example, to prove that the second player may
not have a winning strategy.

The main concepts of the file are:
- `Bait` descirbes a move to be played to allow strategy stealing
  (ie. the first player steals the strategy that the second player
  plays from that move onwards)
- `stolen_strat` describes the stolen strategy
- `pre_stolen_strat` describes a ficticious strategy that mimics
  a strategy played as reponse to the stolen strategy, so as to get
  the proof of strategy stealing to work.
- `Stealing_condition` groups the conditions for strategy stealing to work
- `Strategy_stealing` is the main theorem : if the stealing conditions are
  satisfied, then the second player can't have a winning stragtegy, so that
  in `zSymm_Game_World`, the first player wins, by Zermelo.

-/


/--
A `trap` is a move that is:
- `leg_fst`: legal as a first move
- `leg_imp`: has the property that for all histories, the next moves are legal
  when they were in a history that was preceded by the `trap` move
- `leg_imp'`: has the property that for all histories that have `trap` as first move,
  the next moves are legal if they are wrt. these histories, with the first move skiped.
-/
structure Bait (g : zSymm_Game_World α β) (trap : β) : Prop where
  leg_fst : g.law [] trap
  leg_imp : ∀ hist, ∀ act, g.hist_legal (hist) → g.law (hist ++ [trap]) act → g.law (hist) act
  leg_imp' : ∀ hist, ∀ act, g.hist_legal (hist) → (Z : ¬ hist = []) → hist.getLast Z = trap → Turn_fst (hist.length + 1) → g.law hist.dropLast act → g.law hist act



lemma Bait_leg_hist (hb : Bait g trap) : ∀ hist, g.hist_legal (hist ++ [trap]) → g.hist_legal (hist) :=
  by
  intro hist leg
  dsimp [Symm_Game_World.hist_legal] at *
  induction' hist with x l ih
  · apply Game_World.hist_legal.nil
  · apply Game_World.hist_legal.cons
    · dsimp at *
      rw [ite_self]
      cases' leg
      rename_i sofar now
      dsimp at now
      rw [ite_self] at now
      exact hb.leg_imp _ _ (ih sofar) now
    · rw [List.cons_append] at leg
      cases' leg
      rename_i sofar _
      exact ih sofar





open Classical

noncomputable
def stolen_strat (g : zSymm_Game_World α β)
  (trap : β) (hb : Bait g trap) (ws : g.sStrategy) : g.fStrategy :=
  -- assumes ws is the supposed winning strategy of the second player we want to steal
  fun h ht hl =>  if M : g.hist_legal (h ++ [trap])
                  then  let move := (ws (h ++ [trap]) (by rw [List.length_append, List.length_singleton, ← Turn_fst_snd_step] ; exact ht) M)
                        -- given a history, we consider the response move of the winning strat in a ficticious
                        -- history where the trap was played, and play it.
                        ⟨move.val, hb.leg_imp h move.val hl (move.prop)⟩
                  else g.toGame_World.exStrat_fst g.hgp h ht hl
                  -- we explect the condition to be true, so we spam default moves here

noncomputable
def pre_stolen_strat (g : zSymm_Game_World α β)
  (trap : β) (hb : Bait g trap) (s_strat : g.sStrategy) : g.fStrategy :=
  -- s_strat is expected to play against the stolen strategy ;
  -- This strategy mimics it as a `fStrategy`, playing the `trap` as first move, then copying s_strat
  fun h ht hl =>  if Z : h = []
                  then  ⟨trap, (by rw [Z] ; exact hb.leg_fst)⟩
                        -- initially, play `trap`
                  else  if M : h.getLast Z = trap
                        then  let move := s_strat h.dropLast (by rw [List.length_dropLast, Nat.sub_add_cancel, Turn_snd_fst_step] ; exact ht ; rw [Nat.succ_le, List.length_pos] ; exact Z) (by have := List.dropLast_append_getLast Z ; rw [M] at this ; apply Bait_leg_hist hb ; rw [this] ; exact hl)
                              -- play the response of s_strat in a history that ignores `trap`
                              ⟨move.val, hb.leg_imp' h move.val hl Z M ht move.prop⟩
                        else  g.toGame_World.exStrat_fst g.hgp h ht hl




/--
A game satisfies the stealing condition if:
- it has a `trap` that serves as bait
- the initial state is not a winning state of the second player
- histories that start with `trap` and yield second wins yield first wins if `trap` is skipped
-/
structure Stealing_condition (g : zSymm_Game_World α β) where
  trap : β
  hb : Bait g trap
  fst_not_win : ¬ g.snd_win_states []
  wb : ∀ hist, g.hist_legal hist → g.snd_win_states (hist ++ [trap]) → g.fst_win_states hist


lemma History_of_stealing (g : zSymm_Game_World α β) (s : Stealing_condition g)
  (ws s_strat : g.toGame_World.sStrategy) (T : Nat) :
  let sto_strat := stolen_strat g s.trap s.hb ws
  let pre_sto_strat := pre_stolen_strat g s.trap s.hb s_strat
  (g.toGame_World.hist_on_turn pre_sto_strat ws (T + 1)).val =
  (g.toGame_World.hist_on_turn sto_strat s_strat T).val ++ [s.trap] :=
  by
  intro sto_strat pre_sto_strat
  induction' T with T ih
  · dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
    rw [dif_pos (by decide)]
    dsimp
    unfold pre_stolen_strat
    rw [dif_pos (by rfl)]
  · by_cases q : Turn_fst ((Nat.succ T))
    · dsimp [Symm_Game_World.hist_on_turn] at *
      rw [g.toGame_World.hist_on_turn_fst_to_snd  _ _ _ q]
      rw [← Turn_snd_fst_step] at q
      rw [g.toGame_World.hist_on_turn_snd_to_fst sto_strat _ _ q]
      congr 1
      dsimp only [sto_strat, stolen_strat]
      rw [dif_pos (by rw [← ih] ; exact (g.toGame_World.hist_on_turn pre_sto_strat ws (T + 1)).prop.1)]
      dsimp
      rename_i q'
      have dtt : (ws (g.toGame_World.hist_on_turn pre_sto_strat ws (T + 1)).val (by rw [g.toGame_World.hist_on_turn_length, ← Turn_fst_snd_step] ; exact q') (g.toGame_World.hist_on_turn pre_sto_strat ws (T + 1)).prop.1).val = (ws (g.toGame_World.hist_on_turn pre_sto_strat ws (T + 1)).val (by rw [g.toGame_World.hist_on_turn_length, ← Turn_fst_snd_step] ; exact q') (g.toGame_World.hist_on_turn pre_sto_strat ws (T + 1)).prop.1).val := rfl
      convert dtt
      · rw [ih]
      · rw [ih]
    · dsimp [Symm_Game_World.hist_on_turn] at *
      rw [g.toGame_World.hist_on_turn_snd_to_fst _ _ _ q]
      rw [Turn_not_fst_iff_snd, ← Turn_fst_snd_step] at q
      rw [g.toGame_World.hist_on_turn_fst_to_snd sto_strat _ _ q]
      congr 1
      dsimp only [pre_sto_strat, pre_stolen_strat]
      rw [dif_neg (by apply g.toGame_World.hist_on_turn_nonempty_of_succ)]
      rw [dif_pos (by simp_rw [ih] ; rw [List.getLast_append])]
      dsimp
      rename_i q'
      rw [Turn_not_fst_iff_snd] at q'
      have dtt : (s_strat (g.toGame_World.hist_on_turn sto_strat s_strat (T)).val (by rw [g.toGame_World.hist_on_turn_length] ; exact q') (g.toGame_World.hist_on_turn sto_strat s_strat (T)).prop.1).val = (s_strat (g.toGame_World.hist_on_turn sto_strat s_strat (T)).val (by rw [g.toGame_World.hist_on_turn_length] ; exact q') (g.toGame_World.hist_on_turn sto_strat s_strat (T)).prop.1).val := rfl
      convert dtt
      all_goals
      · rw [ih, List.dropLast_append_of_ne_nil _ (List.noConfusion)]
        dsimp
        rw [List.append_nil]



theorem Strategy_stealing (g : zSymm_Game_World α β) (s : Stealing_condition g) : g.is_fst_win :=
  by
  cases' g.Zermelo with F S
  · exact F
  · obtain ⟨ws, ws_prop⟩ := S
    let sto_strat := stolen_strat g s.trap s.hb ws
    use sto_strat
    intro s_strat
    let pre_sto_strat := pre_stolen_strat g s.trap s.hb s_strat
    specialize ws_prop pre_sto_strat
    obtain ⟨T,Tw,Tn⟩ := ws_prop
    apply Game.coherent_end_fst_win _ (by apply g.hgn)
    cases' T with T
    · dsimp [Game.hist_on_turn, Game_World.hist_on_turn] at Tw
      exfalso
      exact s.fst_not_win Tw
    · use T
      dsimp at Tw Tn
      dsimp
      apply s.wb _ (g.toGame_World.hist_on_turn sto_strat s_strat T).prop.1
      convert Tw
      rw [← History_of_stealing]
      dsimp [Game.hist_on_turn]
      rfl
