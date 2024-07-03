/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Conditioning_Symm
import Mathlib.Tactic







lemma zSymm_Game_World.init_WL_of_turn_zero_WL
  (g : zSymm_Game_World α β)
  (f_strat s_strat : Strategy α β):
  g.Turn_isWL f_strat s_strat 0 → g.win_states g.init_game_state :=
  by
  dsimp [Symm_Game_World.Turn_isWL, Symm_Game_World.state_on_turn]
  intro t0
  exact t0



lemma zSymm_Game_World.conditioning_bound
  (g : zSymm_Game_World α β)
  {T : ℕ} (hg : g.isWL_wBound (T + 1))
  (fst_act : β) (leg : g.law g.init_game_state [] fst_act) :
  (g.toSymm_Game_World.world_after_fst fst_act).isWL_wBound T :=
  by
  have nt := g.coherent
  have b := Symm_Game_World.strong_legal_blind_toWeak _ (Symm_Game_World.hyper_legal_blind_toStrong _ g.is_hyper_legal_blind)
  have tb := Symm_Game_World.strong_transition_blind_toWeak _ (Symm_Game_World.hyper_transition_blind_toStrong _ g.is_hyper_transition_blind)
  intro f_strat s_strat f_leg s_leg
  let fst_strat : Strategy α β := fst_strat_deconditioned s_strat fst_act g.toSymm_Game_World
  let snd_strat : Strategy α β := snd_strat_deconditioned f_strat fst_act g.toSymm_Game_World
  have fst_leg :=  g.law_deconditioned_fst fst_act leg  f_strat s_strat s_leg b.1
  have snd_leg := g.law_deconditioned_snd fst_act leg  f_strat s_strat f_leg b.2
  specialize hg fst_strat snd_strat fst_leg snd_leg
  obtain ⟨t, t_bd, t_prop⟩ := hg
  cases' t with t
  · use 0
    constructor
    · exact Nat.zero_le T
    · dsimp [Symm_Game_World.Turn_isWL] at *
      dsimp [Symm_Game_World.state_on_turn]
      have := (nt fst_strat snd_strat fst_leg snd_leg 0) t_prop
      dsimp [Symm_Game_World.state_on_turn] at this
      dsimp [Symm_Game_World.history_on_turn, History_on_turn, fst_strat_deconditioned] at this
      rw [if_pos (by rfl)] at this
      exact this
  · rw [Nat.succ_le_succ_iff] at t_bd
    use t
    constructor
    · exact t_bd
    · dsimp [Symm_Game_World.Turn_isWL] at *
      rw [← Symm_Game_World.State_of_deconditioned]
      · apply t_prop
      · exact tb
      · exact leg




lemma zSymm_Game_World.conditioning_WL_helper
  (g : zSymm_Game_World α β)
  (hWL : g.has_WL)
  (hnfw : ¬ g.is_snd_win) :
  g.is_fst_win :=
  by
  cases' hWL
  · assumption
  · contradiction




lemma zSymm_Game_World.conditioning_WL
  [Inhabited β]
  (g : zSymm_Game_World α β)
  (h : ∀ fst_act : β, (hl : g.law g.init_game_state [] fst_act) → (g.world_after_fst fst_act hl).has_WL)
  :
  g.has_WL :=
  by
  classical
  apply g.has_WL_init_end _ h
  rintro ⟨_,wlg⟩
  by_cases qws : ∃ f_act : β, ∃ (hl : g.law g.init_game_state [] f_act), (g.world_after_fst f_act hl).is_snd_win
  · obtain ⟨f_act, f_act_leg, ws, ws_prop⟩ := qws
    apply zSymm_Game_World.has_WL.wf
    use (g.snd_strat_reconditioned ws f_act f_act_leg)
    intro snd_s snd_leg
    specialize ws_prop (g.fst_strat_reconditioned snd_s f_act)
    --specialize ws_prop (by apply zSymm_Game_World.snd_reconditioned_legal ; exact ws_leg)
    specialize ws_prop (by apply g.fst_reconditioned_legal f_act f_act_leg snd_s ws ; exact snd_leg )
    obtain ⟨ws_leg, ws_prop⟩ := ws_prop
    constructor
    · apply g.reCondition_win
      · exact wlg
      · exact ws_prop
    · apply zSymm_Game_World.snd_reconditioned_legal'
      exact ws_leg
  · push_neg at qws
    apply zSymm_Game_World.has_WL.ws
    let ws_aux (hi : List β) (hne : hi ≠ [])  (hil : g.law g.init_game_state [] (hi.getLast hne)) :=
      let f_act := List.getLast hi hne
      (Classical.choose ((g.world_after_fst f_act hil).conditioning_WL_helper
                                                            (h f_act hil)
                                                            (qws f_act hil)
                                                            --(qd f_act hil))
                                                            ))
    let ws : Strategy α β := fun (_ : α) hist  =>
                              if hh : hist = [] -- shouldn't happen, as snd strat
                              then default -- dummy
                              else let f_act := List.getLast hist hh
                                    if H : g.law g.init_game_state [] f_act-- should be the cases ?!?
                                    then (ws_aux hist hh H)
                                          (g.transition g.init_game_state [] f_act) hist.dropLast -- is it ? since ref to history in current game
                                    else default
    use ws
    intro f_strat f_leg
    let f_act := f_strat g.init_game_state []
    have f_act_leg := f_leg 0 (by decide)
    dsimp [History_on_turn] at f_act_leg

    have fix : ∀ (h H : List β) (hne : h ≠ []) (Hne : H ≠ [])
              (hl : Game_World.fst_legal g.toGame_World g.init_game_state [] (List.getLast h hne))
              (Hl : Game_World.fst_legal g.toGame_World g.init_game_state [] (List.getLast H Hne)),
              List.getLast h hne = List.getLast H Hne → ws_aux h hne hl = ws_aux H Hne Hl :=
      by
      intro h H hne Hne hl Hl main
      dsimp [ws_aux]
      simp_rw [main]
    have proof := ((g.world_after_fst f_act f_act_leg).conditioning_WL_helper
                                      (h f_act f_act_leg)
                                      (qws f_act f_act_leg)
                                      --(qd f_act f_act_leg)
                                      )
    have da_prop := Classical.choose_spec proof
    specialize da_prop (g.snd_strat_conditioned f_strat f_act)
    specialize da_prop (by
                        have := g.conditioned_legal_fst f_strat ws_aux fix f_act_leg
                        dsimp [ws_aux] at this
                        simp_rw [zSymm_Game_World.world_after_fst_law]
                        rw [← this]
                        apply Strategy_legal_fst_eq_strats_snd g f_strat ws (g.fst_strat_conditioned ws_aux)
                        · intro t ts
                          cases' t with t
                          · contradiction
                          · dsimp [ws, fst_strat_conditioned]
                            rw [dif_neg (by apply History_on_turn_nonempty_of_succ)]
                            rw [History_on_turn_getLast_fst_act]
                            rw [dif_pos f_act_leg]
                            rw [dif_neg (by apply History_on_turn_nonempty_of_succ)]
                            rw [History_on_turn_getLast_fst_act]
                            rw [dif_pos f_act_leg]
                            rfl
                        · exact f_leg
                        )
    obtain ⟨ws_leg, da_prop⟩ := da_prop
    constructor
    · apply Conditioning_win
      · exact wlg
      · apply da_prop
      · exact fix
    · have := g.conditioned_legal_snd f_strat ws_aux fix f_act_leg
      dsimp [ws_aux, fst_strat_conditioned] at this
      dsimp [ws]
      rw [g.fst_strat_conditioned_get_rw_to_work _] at this
      rw [ this]
      apply ws_leg





lemma zSymm_Game_World.Zermelo
  [Inhabited β]
  (g : zSymm_Game_World α β)
  {T : ℕ} (hg : g.isWL_wBound T)
  : g.has_WL :=
  by
  revert g
  induction' T with t ih
  · intro g t0
    dsimp [Game_World.isWL_wBound] at t0
    -- obtain ⟨s_strat, s_prop⟩ := g.playable_has_strong_snd_strat g.playable
    -- obtain ⟨ f_strat, f_leg⟩ := g.playable_has_Fst_strat g.playable s_strat
    -- let s_leg := s_prop f_strat f_leg
    --obtain ⟨t, tl0, t_end⟩ := t0 f_strat s_strat f_leg s_leg
    obtain ⟨t, tl0, t_end⟩ := t0 (exStrat g.law g.playable) (exStrat g.law g.playable) (g.playable_has_strat_explicit g.playable).1 (g.playable_has_strat_explicit g.playable).2
    rw [Nat.le_zero] at tl0
    rw [tl0] at t_end
    replace t_end := g.init_WL_of_turn_zero_WL (exStrat g.law g.playable) (exStrat g.law g.playable) t_end
    apply zSymm_Game_World.has_WL.ws
    use (exStrat g.law g.playable)
    intro f_strat' f_leg'
    constructor
    · use 0
      constructor
      · decide
      · constructor
        · dsimp [Game.state_on_turn]
          exact t_end
        · intro t ahhh ; contradiction
    · exact (g.playable_has_strong_snd_strat g.playable) f_strat' f_leg'
  · intro g bd
    apply zSymm_Game_World.conditioning_WL
    intro f_act f_leg
    apply ih
    exact zSymm_Game_World.conditioning_bound g bd f_act f_leg
