
/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Games.gameLib.ConwayInduction


private lemma Game_World.has_WL_helper (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) :
  g.has_staged_WL hist leg → (¬ g.is_fst_staged_win hist leg) → g.is_snd_staged_win hist leg := by
  intro m c
  cases' m with m m
  · exfalso ; exact c m
  · exact m

private lemma Game_World.has_WL_helper' (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hist : List β) (leg : g.hist_legal hist) :
  g.has_staged_WL hist leg → (¬ g.is_snd_staged_win hist leg) → g.is_fst_staged_win hist leg := by
  intro m c
  cases' m with m m
  · exact m
  · exfalso ; exact c m



lemma Game_World.conditioning_step [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hgw : g.isWL) (hgp : g.playable) (hgn : g.coherent_end)
  (hist : List β) (Leg : g.hist_legal hist) :
  g.has_staged_WL hist Leg :=
  by
  apply g.ConwayInduction hgw hgp hgn g.has_staged_WL hist Leg
  intro h leg ih
  by_cases N : g.hist_neutral  h
  · by_cases T : Turn_fst (h.length+1)
    · by_cases q : ∃ f_act : β, ∃ (al : g.fst_legal h f_act), (g.is_fst_staged_win (f_act :: h) (Game_World.hist_legal.cons h f_act (by rw [if_pos T] ; exact al) leg))
      · obtain ⟨f_act, al, ws, ws_prop⟩ := q
        apply Game_World.has_staged_WL.wf
        let ws' : g.fStrat_wHist h leg := ⟨ws.val , (g.fStrat_staged_cons_1  _ _ _ leg al rfl T ws.prop)⟩
        use ws'
        intro s_strat
        specialize ws_prop ⟨s_strat.val, by apply g.sStrat_staged_cons_2 _ _ _ leg al rfl T s_strat.prop⟩
        apply ws_prop
      · push_neg at q
        have main' : ∀ (f_act : β) (al : g.fst_legal h f_act), g.is_snd_staged_win (f_act :: h) (Game_World.hist_legal.cons h f_act (by rw [if_pos T] ; exact al) leg) :=
          by
          intro f_act al
          have leg' := (Game_World.hist_legal.cons h f_act (by rw [if_pos T] ; exact al) leg)
          specialize ih (f_act :: h)
          specialize q f_act al
          by_cases Q : (g.hist_neutral (f_act :: h))
          · exact g.has_WL_helper (f_act :: h) leg'
              (by
               apply ih
               constructor
               · use f_act
               · exact Q
               · exact leg'
              ) q
          · simp_rw [g.hist_neutral_and, not_and_or, not_not] at Q
            cases' Q with Q Q
            · exfalso
              apply q
              apply g.staged_WL_of_win_state_fst hgp hgn _ _ Q
            · apply g.staged_WL_of_win_state_snd hgp hgn _ _ Q
        apply Game_World.has_staged_WL.ws
        use sStrat_winner g hgp h leg T main'
        intro f_strat
        apply sStrat_winner_wins
    · by_cases q : ∃ f_act : β, ∃ (al : g.snd_legal h f_act), (g.is_snd_staged_win (f_act :: h) (Game_World.hist_legal.cons h f_act (by rw [if_neg T] ; exact al) leg))
      · obtain ⟨f_act, al, ws, ws_prop⟩ := q
        apply Game_World.has_staged_WL.ws
        let ws' : g.sStrat_wHist h leg := ⟨ws.val , (g.sStrat_staged_cons_1 _ _ _ leg al rfl T ws.prop)⟩
        use ws'
        intro s_strat
        specialize ws_prop ⟨s_strat.val, by apply g.fStrat_staged_cons_2 _ _ _ leg al rfl T s_strat.prop⟩
        apply ws_prop
      · push_neg at q
        have main' : ∀ (f_act : β) (al : g.snd_legal h f_act), g.is_fst_staged_win (f_act :: h) (Game_World.hist_legal.cons h f_act (by rw [if_neg T] ; exact al) leg) :=
          by
          intro f_act al
          have leg' := (Game_World.hist_legal.cons h f_act (by rw [if_neg T] ; exact al) leg)
          specialize ih (f_act :: h)
          specialize q f_act al
          by_cases Q : (g.hist_neutral (f_act :: h))
          · exact g.has_WL_helper' (f_act :: h) leg'
              (by
               apply ih
               constructor
               · use f_act
               · exact Q
               · exact leg'
              ) q
          · simp_rw [g.hist_neutral_and, not_and_or, not_not] at Q
            cases' Q with Q Q
            · apply g.staged_WL_of_win_state_fst hgp hgn _ _ Q
            · exfalso
              apply q
              apply g.staged_WL_of_win_state_snd hgp hgn _ _ Q
        apply Game_World.has_staged_WL.wf
        use fStrat_winner g hgp h leg T main'
        intro f_strat
        apply fStrat_winner_wins
  · unfold hist_neutral at N
    simp_rw [g.hist_neutral_and, not_and_or, not_not] at N
    apply g.staged_WL_of_win_state hgp hgn _ _ N


-- # Zermelo


lemma Game_World.Zermelo [DecidableEq β] (g : Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hgw : g.isWL) (hgp : g.playable) (hgn : g.coherent_end) :
  g.has_WL :=
  by
  have := g.conditioning_step hgw hgp hgn [] Game_World.hist_legal.nil
  rw [g.has_WL_iff_has_staged_WL_empty]
  exact this

lemma Symm_Game_World.Zermelo [DecidableEq β] (g : Symm_Game_World α β)
  [DecidablePred (g.fst_win_states)] [DecidablePred (g.snd_win_states )]
  (hgw : g.isWL) (hgp : g.playable) (hgn : g.coherent_end ) :
  g.has_WL := by dsimp [Symm_Game_World.has_WL] ; convert @Game_World.Zermelo _ _ _ g.toGame_World (by rwa [Symm_Game_World.toGame_World_fst_win]) (by rwa [Symm_Game_World.toGame_World_snd_win]) (by convert hgw) hgp hgn

open Classical


structure zGame_World (α β : Type _) [DecidableEq β] extends Game_World α β where
  (hgw : toGame_World.isWL) (hgp : toGame_World.playable) (hgn : toGame_World.coherent_end)

structure zSymm_Game_World (α β : Type _) extends Symm_Game_World α β where
  (hgw : toSymm_Game_World.isWL) (hgp : toSymm_Game_World.playable) (hgn : toSymm_Game_World.coherent_end)

lemma zGame_World.Zermelo (g : zGame_World α β) : g.has_WL := g.toGame_World.Zermelo g.hgw g.hgp g.hgn

lemma zSymm_Game_World.Zermelo (g : zSymm_Game_World α β) : g.has_WL := g.toSymm_Game_World.Zermelo g.hgw g.hgp g.hgn
