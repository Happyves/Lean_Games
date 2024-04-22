/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Conditioning
import Mathlib.Tactic







lemma zGame_World.init_WL_of_turn_zero_WL
  (g : zGame_World α β)
  (f_strat s_strat : Strategy α β):
  g.Turn_isWL f_strat s_strat 0 → g.snd_win_states g.init_game_state :=
  by
  intro t0
  cases' t0 with wf ws
  · contradiction
  · rename_i h
    dsimp [Game_World.state_on_turn] at h
    exact h



lemma zGame_World.conditioning_bound
  (g : zGame_World α β)
  {T : ℕ} (hg : g.isWL_wBound (T + 1))
  (fst_act : β) (leg : g.fst_legal g.init_game_state [] fst_act) :
  (g.toGame_World.world_after_fst fst_act).isWL_wBound T :=
  by
  have nt := g.coherent
  have b := Game_World.strong_legal_blind_toWeak _ (Game_World.hyper_legal_blind_toStrong _ g.is_hyper_legal_blind)
  have tb := Game_World.strong_transition_blind_toWeak _ (Game_World.hyper_transition_blind_toStrong _ g.is_hyper_transition_blind)
  intro f_strat s_strat f_leg s_leg
  let fst_strat : Strategy α β := fst_strat_deconditioned s_strat fst_act g.toGame_World
  let snd_strat : Strategy α β := snd_strat_deconditioned f_strat fst_act g.toGame_World
  specialize hg fst_strat snd_strat _ _
  · apply g.fst_legal_deconditioned fst_act leg  f_strat s_strat s_leg b.1
  · apply g.snd_legal_deconditioned fst_act leg  f_strat s_strat f_leg b.2
  · obtain ⟨t, t_bd, t_prop⟩ := hg
    cases' t with t
    · use 0
      constructor
      · exact Nat.zero_le T
      · cases' t_prop
        · rename_i no pe ; contradiction
        · rename_i c
          apply Game_World.Turn_isWL.ws
          · decide
          · dsimp [Game_World.state_on_turn]
            have := (nt fst_strat snd_strat 0).s c
            dsimp [Game_World.state_on_turn] at this
            rw [if_pos (by decide)] at this
            dsimp [Game_World.history_on_turn, History_on_turn, fst_strat_deconditioned] at this
            rw [if_pos (by rfl)] at this
            exact this
    · rw [Nat.succ_le_succ_iff] at t_bd
      use t
      constructor
      · exact t_bd
      · cases' t_prop with tp c tp c c
        · apply Game_World.Turn_isWL.ws
          · rw [Turn_snd_fst_step] ; exact tp
          · rw [← Game_World.State_of_deconditioned]
            · rw [Game_World.world_after_fst_snd_win_states]
              rw [g.sym_win] at c
              exact c
            · exact tb
            · exact leg
        · apply Game_World.Turn_isWL.wf
          · rw [Turn_fst_snd_step] ; exact tp
          · rw [← Game_World.State_of_deconditioned]
            · rw [Game_World.world_after_fst_fst_win_states]
              rw [← g.sym_win] at c
              exact c
            · exact tb
            · exact leg




lemma zGame_World.conditioning_WL_helper
  (g : zGame_World α β)
  (hWL : g.has_WL)
  (hnfw : ¬ g.is_snd_win) :
  g.is_fst_win :=
  by
  cases' hWL
  · assumption
  · contradiction




lemma zGame_World.conditioning_WL
  [Inhabited β]
  (g : zGame_World α β)
  (h : ∀ fst_act : β, (hl : g.fst_legal g.init_game_state [] fst_act) → (g.world_after_fst fst_act hl).has_WL)
  :
  g.has_WL :=
  by
  classical
  apply g.has_WL_init_end _ h
  rintro ⟨_,wlg⟩
  by_cases qws : ∃ f_act : β, ∃ (hl : g.fst_legal g.init_game_state [] f_act), (g.world_after_fst f_act hl).is_snd_win
  · obtain ⟨f_act, f_act_leg, ws, ws_prop⟩ := qws
    apply zGame_World.has_WL.wf
    use (g.snd_strat_reconditioned ws f_act f_act_leg)
    intro snd_s ws_leg snd_leg
    specialize ws_prop (g.fst_strat_reconditioned snd_s f_act)
    specialize ws_prop (by apply zGame_World.snd_reconditioned_legal ; exact ws_leg)
    specialize ws_prop (by apply g.fst_reconditioned_legal f_act f_act_leg snd_s ws ; exact snd_leg )
    apply g.reCondition_win
    · exact wlg
    · exact ws_prop
  · push_neg at qws
    apply zGame_World.has_WL.ws
    let ws_aux (hi : List β) (hne : hi ≠ [])  (hil : g.fst_legal g.init_game_state [] (hi.getLast hne)) :=
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
                                    if H : g.fst_legal g.init_game_state [] f_act-- should be the cases ?!?
                                    then (ws_aux hist hh H)
                                          (g.fst_transition g.init_game_state [] f_act) hist.dropLast -- is it ? since ref to history in current game
                                    else default
    use ws
    intro f_strat ws_leg f_leg
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
                        have := g.conditioned_legal_snd f_strat ws_aux fix f_act_leg
                        dsimp [ws_aux] at this
                        simp_rw [zGame_World.world_after_fst_fst_legal]
                        rw [← this]
                        apply Strategy_legal_snd_eq_strats_snd g f_strat ws (g.fst_strat_conditioned ws_aux)
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
                        · exact ws_leg
                        )
    specialize da_prop (by
                        have := g.conditioned_legal_fst f_strat ws_aux fix f_act_leg
                        dsimp [ws_aux] at this
                        simp_rw [zGame_World.world_after_fst_snd_legal]
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
    apply Conditioning_win
    · exact wlg
    · apply da_prop
    · exact fix






lemma zGame_World.Zermelo
  [Inhabited β]
  (g : zGame_World α β)
  {T : ℕ} (hg : g.isWL_wBound T)
  : g.has_WL :=
  by
  revert g
  induction' T with t ih
  · intro g t0
    dsimp [Game_World.isWL_wBound] at t0
    obtain ⟨f_strat, s_strat, f_leg, s_leg⟩ := g.playable_has_strat g.playable
    obtain ⟨t, tl0, t_end⟩ := t0 f_strat s_strat f_leg s_leg
    rw [Nat.le_zero] at tl0
    rw [tl0] at t_end
    replace t_end := g.init_WL_of_turn_zero_WL f_strat s_strat t_end
    apply zGame_World.has_WL.ws
    use (fun _ _ => default)
    intro f_strat' leg f_leg'
    use 0
    constructor
    · decide
    · constructor
      · dsimp [Game.state_on_turn]
        exact t_end
      · intro t ahhh ; contradiction
  · intro g bd
    apply zGame_World.conditioning_WL
    intro f_act f_leg
    apply ih
    exact zGame_World.conditioning_bound g bd f_act f_leg
