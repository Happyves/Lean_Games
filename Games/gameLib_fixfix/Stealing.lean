/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Games.gameLib_fixfix.Zermelo




structure Bait (g : zSymm_Game_World α β) (trap : β) : Prop where
  leg_fst : g.law g.init_game_state [] trap
  leg_imp : ∀ hist, ∀ act, Hist_legal g.init_game_state g.law g.law (hist) → g.law g.init_game_state (hist ++ [trap]) act → g.law g.init_game_state (hist) act
  leg_imp' : ∀ hist, ∀ act, Hist_legal g.init_game_state g.law g.law (hist) → (Z : ¬ hist = []) → hist.getLast Z = trap → Turn_fst (hist.length + 1) → g.law g.init_game_state hist.dropLast act → g.law g.init_game_state hist act



lemma Bait_leg_hist (hb : Bait g trap) : ∀ hist, Hist_legal g.init_game_state g.law g.law (hist ++ [trap]) → Hist_legal g.init_game_state g.law g.law (hist) :=
  by
  intro hist leg
  induction' hist with x l ih
  · apply Hist_legal.nil
  · apply Hist_legal.cons
    · rw [ite_self]
      rw [List.cons_append] at leg
      cases' leg
      rename_i sofar now
      rw [ite_self] at now
      exact hb.leg_imp _ _ (ih sofar) now
    · rw [List.cons_append] at leg
      cases' leg
      rename_i sofar _
      exact ih sofar





open Classical

noncomputable
def stolen_strat (g : zSymm_Game_World α β)
  (trap : β) (hb : Bait g trap) (ws : sStrategy g.init_game_state g.law g.law) : fStrategy g.init_game_state g.law g.law :=
  fun h ht hl =>  if M : Hist_legal g.init_game_state g.law g.law (h ++ [trap])
                  then  let move := (ws (h ++ [trap]) (by rw [List.length_append, List.length_singleton, ← Turn_fst_snd_step] ; exact ht) M)
                        ⟨move.val, hb.leg_imp h move.val hl (move.prop)⟩
                  else g.exStrat_fst g.hgp h ht hl

noncomputable
def pre_stolen_strat (g : zSymm_Game_World α β)
  (trap : β) (hb : Bait g trap) (s_strat : sStrategy g.init_game_state g.law g.law) : fStrategy g.init_game_state g.law g.law :=
  fun h ht hl =>  if Z : h = []
                  then ⟨trap, (by rw [Z] ; exact hb.leg_fst)⟩
                  else  if M : h.getLast Z = trap
                        then  let move := s_strat h.dropLast (by rw [List.length_dropLast, Nat.sub_add_cancel, Turn_snd_fst_step] ; exact ht ; rw [Nat.succ_le, List.length_pos] ; exact Z) (by have := List.dropLast_append_getLast Z ; rw [M] at this ; apply Bait_leg_hist hb ; rw [this] ; exact hl)
                              ⟨move.val, hb.leg_imp' h move.val hl Z M ht move.prop⟩
                        else  g.exStrat_fst g.hgp h ht hl




--#exit

structure Stealing_condition (g : zSymm_Game_World α β) where
  trap : β
  hb : Bait g trap
  fst_not_win : ¬ g.snd_win_states g.init_game_state []
  wb : ∀ hist, Hist_legal g.init_game_state g.law g.law hist → g.snd_win_states g.init_game_state (hist ++ [trap]) → g.fst_win_states g.init_game_state hist


lemma History_of_stealing (g : zSymm_Game_World α β) (s : Stealing_condition g)
  (ws s_strat : sStrategy g.init_game_state g.law g.law) (T : Nat) :
  let sto_strat := stolen_strat g s.trap s.hb ws
  let pre_sto_strat := pre_stolen_strat g s.trap s.hb s_strat
  (History_on_turn g.init_game_state g.law g.law pre_sto_strat ws (T + 1)).val =
  (History_on_turn g.init_game_state g.law g.law sto_strat s_strat T).val ++ [s.trap] :=
  by
  intro sto_strat pre_sto_strat
  induction' T with T ih
  · dsimp [History_on_turn]
    rw [dif_pos (by decide)]
    dsimp
    unfold pre_stolen_strat
    rw [dif_pos (by rfl)]
  · by_cases q : Turn_fst ((Nat.succ T))
    · rw [History_on_turn_fst_to_snd g.init_game_state g.law g.law _ _ _ q]
      rw [← Turn_snd_fst_step] at q
      rw [History_on_turn_snd_to_fst g.init_game_state g.law g.law sto_strat _ _ q]
      congr 1
      dsimp only [sto_strat, stolen_strat]
      rw [dif_pos (by  rw [← ih] ; exact (History_on_turn g.init_game_state g.law g.law pre_sto_strat ws (T + 1)).prop.1)]
      dsimp
      rename_i q'
      have dtt : (ws (History_on_turn g.init_game_state g.law g.law pre_sto_strat ws (T + 1)).val (by rw [History_on_turn_length, ← Turn_fst_snd_step] ; exact q') (History_on_turn g.init_game_state g.law g.law pre_sto_strat ws (T + 1)).prop.1).val = (ws (History_on_turn g.init_game_state g.law g.law pre_sto_strat ws (T + 1)).val (by rw [History_on_turn_length, ← Turn_fst_snd_step] ; exact q') (History_on_turn g.init_game_state g.law g.law pre_sto_strat ws (T + 1)).prop.1).val := rfl
      convert dtt
      · rw [ih]
      · rw [ih]
    · rw [History_on_turn_snd_to_fst g.init_game_state g.law g.law _ _ _ q]
      rw [Turn_not_fst_iff_snd, ← Turn_fst_snd_step] at q
      rw [History_on_turn_fst_to_snd g.init_game_state g.law g.law sto_strat _ _ q]
      congr 1
      dsimp only [pre_sto_strat, pre_stolen_strat]
      rw [dif_neg (by apply History_on_turn_nonempty_of_succ)]
      rw [dif_pos (by simp_rw [ih] ; rw [List.getLast_append])]
      dsimp
      rename_i q'
      rw [Turn_not_fst_iff_snd] at q'
      have dtt : (s_strat (History_on_turn g.init_game_state g.law g.law sto_strat s_strat (T)).val (by rw [History_on_turn_length] ; exact q') (History_on_turn g.init_game_state g.law g.law sto_strat s_strat (T)).prop.1).val = (s_strat (History_on_turn g.init_game_state g.law g.law sto_strat s_strat (T)).val (by rw [History_on_turn_length] ; exact q') (History_on_turn g.init_game_state g.law g.law sto_strat s_strat (T)).prop.1).val := rfl
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
    · dsimp [History_on_turn] at Tw
      exfalso
      exact s.fst_not_win Tw
    · use T
      dsimp at Tw Tn
      dsimp
      apply s.wb _ (History_on_turn g.init_game_state g.law g.law sto_strat s_strat T).prop.1
      convert Tw
      rw [History_of_stealing]
