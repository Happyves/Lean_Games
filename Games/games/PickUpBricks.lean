/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.exLib.Nat
import Games.gameLib.Basic
import Mathlib.Tactic


variable (init_bricks : ℕ)

abbrev bricks_start_turn_from_ini_hist (ini : ℕ) (hist : List ℕ) := ini - hist.sum

abbrev bricks_end_turn_from_ini_hist_act (ini : ℕ) (hist : List ℕ) (act : ℕ) := ini - hist.sum - act

lemma bricks_start_end (ini : ℕ) (hist : List ℕ) (act : ℕ) :
  bricks_end_turn_from_ini_hist_act ini hist act = (bricks_start_turn_from_ini_hist ini hist) - act :=
  by rfl

lemma bricks_add_zero (ini : ℕ) (hist : List ℕ) :
  bricks_end_turn_from_ini_hist_act ini hist 0 = bricks_start_turn_from_ini_hist ini hist :=
  by
  rfl

lemma bricks_start_cons (ini : ℕ) (hist : List ℕ) (x : ℕ) :
  bricks_start_turn_from_ini_hist ini (x :: hist) = bricks_start_turn_from_ini_hist ini hist - x :=
  by
  dsimp [bricks_start_turn_from_ini_hist]
  rw [List.sum_cons]
  rw [add_comm, Nat.sub_add_eq]


def PickUpBricks : Symm_Game_World ℕ ℕ where
  init_game_state := init_bricks
  win_states := (fun n => n = 0)
  transition := bricks_end_turn_from_ini_hist_act init_bricks
  law := fun hist act => match M : (bricks_start_turn_from_ini_hist init_bricks hist) with
                             | 0 => act = 0
                             | 1 => act = 1
                             | _ => act = 1 ∨ act = 2

lemma PUB_state_bricks {g : Symm_Game ℕ ℕ} {n : ℕ} (h : g.toSymm_Game_World = PickUpBricks n) :
  ∀ turn : ℕ, bricks_start_turn_from_ini_hist n (History_on_turn n g.fst_strat g.snd_strat turn) =
  g.state_on_turn turn :=
  by
  intro t
  induction' t with t _
  · dsimp [bricks_start_turn_from_ini_hist, History_on_turn,  Symm_Game.state_on_turn]
    rw [h]
    rw [PickUpBricks]
  · dsimp [bricks_start_turn_from_ini_hist, History_on_turn]
    split_ifs with ct
    all_goals rw [List.sum_cons]
    all_goals dsimp [Symm_Game.state_on_turn]
    · rw [if_pos ct]
      rw [h]
      dsimp [Symm_Game_World.transition, PickUpBricks]
      rw [bricks_start_end]
      rw [add_comm, Nat.sub_add_eq]
      congr
      all_goals rw [h]
      all_goals rw [PickUpBricks]
    · rw [if_neg ct]
      rw [h]
      dsimp [Symm_Game_World.transition, PickUpBricks]
      rw [bricks_start_end]
      rw [add_comm, Nat.sub_add_eq]
      congr
      all_goals rw [h]
      all_goals rw [PickUpBricks]


def pub_win_strat : List ℕ → ℕ  := -- for fst player ; (is strat ; remeber that init_bricks is section param)
  fun hist =>
    let b := bricks_start_turn_from_ini_hist init_bricks hist
    let d := b % 3
    if b = 0
    then 0
    else if d = 1 then 1 else 2

lemma pub_win_strat_one (h : List ℕ)
  (H0 : bricks_start_turn_from_ini_hist init_bricks h ≠ 0)
  (H1 : bricks_start_turn_from_ini_hist init_bricks h ≠ 1)
  (hs : bricks_start_turn_from_ini_hist init_bricks h % 3 = 0)
  : pub_win_strat init_bricks (1 :: h) = 2 :=
  by
  rw [pub_win_strat]
  dsimp
  have : bricks_start_turn_from_ini_hist init_bricks (1 :: h) ≠ 0 :=
    by
    intro con
    rw [bricks_start_cons] at con
    rw [Nat.sub_eq_zero_iff_le] at con
    interval_cases (bricks_start_turn_from_ini_hist init_bricks h) <;> contradiction
  rw [if_neg this]
  rw [bricks_start_cons]
  split_ifs with c
  · rw [← Nat.add_mod_right] at c
    rw [← Nat.sub_add_comm] at c
    · rw [Nat.add_sub_assoc] at c
      · rw [Nat.add_mod] at c
        rw [hs] at c
        contradiction
      · decide
    · rw [Nat.one_le_iff_ne_zero]
      exact H0
  · rfl

lemma pub_win_strat_two (h : List ℕ)
  (H0 : bricks_start_turn_from_ini_hist init_bricks h ≠ 0)
  (H1 : bricks_start_turn_from_ini_hist init_bricks h ≠ 1)
  (hs : bricks_start_turn_from_ini_hist init_bricks h % 3 = 0)
  : pub_win_strat init_bricks (2 :: h) = 1 :=
  by
  rw [pub_win_strat]
  dsimp
  have : bricks_start_turn_from_ini_hist init_bricks (2 :: h) ≠ 0 :=
    by
    intro con
    rw [bricks_start_cons] at con
    rw [Nat.sub_eq_zero_iff_le] at con
    interval_cases (bricks_start_turn_from_ini_hist init_bricks h) <;> contradiction
  rw [if_neg this]
  rw [bricks_start_cons]
  split_ifs with c
  · rfl
  · rw [← Nat.add_mod_right] at c
    rw [← Nat.sub_add_comm] at c
    · rw [Nat.add_sub_assoc] at c
      · rw [Nat.add_mod] at c
        rw [hs] at c
        contradiction
      · decide
    · rw [Nat.two_le_iff]
      exact ⟨H0,H1⟩



lemma pub_win_strat_legal (s_strat : Strategy ℕ ℕ):
  Strategy_legal
    init_bricks
    (fun _ : ℕ => (PickUpBricks init_bricks).law)
    pub_win_strat
    s_strat
    pub_win_strat
    :=
  by
  dsimp [PickUpBricks, pub_win_strat]
  intro hist
  split
  · rename_i h
    dsimp [pub_win_strat]
    rw [if_pos h]
  · rename_i h
    dsimp [pub_win_strat]
    rw [if_neg _]
    <;> {rw [h] ; decide}
  · rename_i h1 h2
    dsimp [pub_win_strat]
    rw [if_neg _]
    · split_ifs <;> decide
    · apply h1


def toy_strat : List ℕ → ℕ  :=
  fun hist => if bricks_start_turn_from_ini_hist init_bricks hist = 0 then 0 else 1

lemma toy_strat_legal (f_strat : Strategy ℕ ℕ):
  Strategy_legal
    init_bricks
    (fun _ : ℕ => (PickUpBricks init_bricks).law)
    f_strat
    toy_strat
    toy_strat
    :=
  by
  dsimp [PickUpBricks, pub_win_strat]
  intro hist
  split
  · rename_i h
    dsimp [toy_strat]
    rw [if_pos h]
  · rename_i h
    dsimp [toy_strat]
    rw [if_neg _]
    rw [h]
    decide
  · rename_i h1 h2
    dsimp [toy_strat]
    rw [if_neg _]
    · decide
    · apply h1


def PickUpBricks_pubWin_vs_toy : Symm_Game ℕ ℕ :=
  {(PickUpBricks 32) with
   fst_strat := pub_win_strat
   snd_strat := toy_strat
   fst_lawful := pub_win_strat_legal 32 toy_strat
   snd_lawful := toy_strat_legal 32 pub_win_strat
   }


#reduce Symm_Game.state_upto_turn PickUpBricks_pubWin_vs_toy 30

set_option maxRecDepth 10000 in
example : Symm_Game.state_on_turn (PickUpBricks_pubWin_vs_toy) 21 = 0 := by decide


example : PickUpBricks_pubWin_vs_toy.fst_win :=
  by
  rw [Symm_Game.fst_win]
  use 21
  constructor
  · decide
  · constructor
    · simp [Symm_Game.toGame, PickUpBricks_pubWin_vs_toy, PickUpBricks]
      decide
    · intro t tdef
      simp [Symm_Game.state_on_turn_neutral]
      interval_cases t
      all_goals {simp [Symm_Game.toGame, PickUpBricks_pubWin_vs_toy, PickUpBricks] ; decide}



lemma loop_invariant
  (win_hyp : init_bricks % 3 = 1 ∨ init_bricks % 3 = 2)
  (s_strat : Strategy ℕ ℕ)
  (s_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) pub_win_strat s_strat s_strat) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := pub_win_strat
                             fst_lawful := pub_win_strat_legal init_bricks s_strat
                             snd_strat := s_strat
                             snd_lawful := s_law } ;
  ∀ turn, Turn_fst turn → (g.state_on_turn turn) % 3 = 0 :=
  by
  intro g
  apply Invariant_fst
  · dsimp [Symm_Game.state_on_turn]
    rw [if_pos (by decide)]
    dsimp [Symm_Game_World.transition, PickUpBricks, Symm_Game.history_on_turn, bricks_end_turn_from_ini_hist_act, pub_win_strat, bricks_start_turn_from_ini_hist]
    split_ifs with z c
    · rw [z]
      decide
    · rw [Nat.sub_mod_eq_zero_of_mod_eq]
      apply c
    · rw [Nat.sub_mod_eq_zero_of_mod_eq]
      rw [or_comm ,or_iff_not_imp_right] at win_hyp
      exact win_hyp c
  · intro t tf th
    rw [Turn_fst_step] at tf
    rw [Symm_Game.state_on_turn]
    split
    · contradiction
    · rename_i m hm
      rw [Nat.succ_eq_add_one] at hm
      rw [if_pos _]
      swap
      · rw [← hm]
        exact tf
      · norm_num at hm
        rw [← hm]
        rw [Symm_Game.history_on_turn, History_on_turn]
        rw [if_neg _]
        swap
        · rw [← Turn_snd_fst_step]
          rw [← Turn_fst_step] at tf
          rw [Turn_not_snd_iff_fst]
          exact tf
        · dsimp [Strategy_legal] at s_law
          specialize s_law t
          dsimp [PickUpBricks] at s_law
          dsimp [PickUpBricks]
          rw [bricks_start_end]
          split at s_law
          · rename_i _ NoBricks
            rw [s_law]
            convert (Nat.zero_mod 3)
            rw [bricks_start_turn_from_ini_hist, List.sum_cons, Nat.zero_add]
            rw [bricks_start_turn_from_ini_hist] at NoBricks
            rw [NoBricks]
            apply Nat.zero_sub
          · rename_i OneBrick
            exfalso
            have fact : g.toSymm_Game_World = PickUpBricks init_bricks := by rfl
            have := PUB_state_bricks fact t
            rw [← this] at th
            rw [OneBrick] at th
            contradiction
          · rename_i noZero noOne
            cases' s_law with one two
            · rw [one]
              rw [bricks_start_cons]
              have fact : g.toSymm_Game_World = PickUpBricks init_bricks := by rfl
              have := PUB_state_bricks fact t
              rw [← this] at th
              rw [pub_win_strat_one init_bricks (History_on_turn init_bricks pub_win_strat s_strat t) noZero noOne th]
              rw [Nat.sub_sub]
              rw [← Nat.mod_eq_sub_mod]
              · exact th
              · by_contra! k
                interval_cases bricks_start_turn_from_ini_hist init_bricks (History_on_turn init_bricks pub_win_strat s_strat t)
                · contradiction
                · contradiction
                · contradiction
            · rw [two]
              rw [bricks_start_cons]
              have fact : g.toSymm_Game_World = PickUpBricks init_bricks := by rfl
              have := PUB_state_bricks fact t
              rw [← this] at th
              rw [pub_win_strat_two init_bricks (History_on_turn init_bricks pub_win_strat s_strat t) noZero noOne th]
              rw [Nat.sub_sub]
              rw [← Nat.mod_eq_sub_mod]
              · exact th
              · by_contra! k
                interval_cases bricks_start_turn_from_ini_hist init_bricks (History_on_turn init_bricks pub_win_strat s_strat t)
                · contradiction
                · contradiction
                · contradiction

lemma acts_le_bricks
  (f_strat s_strat : Strategy ℕ ℕ)
  (f_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat s_strat) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             fst_lawful := f_law
                             snd_strat := s_strat
                             snd_lawful := s_law } ;
   ∀ turn : ℕ,
  let H := History_on_turn init_bricks f_strat s_strat turn ;
  (f_strat init_bricks H ≤ bricks_start_turn_from_ini_hist init_bricks H)
    ∧ (s_strat init_bricks H ≤ bricks_start_turn_from_ini_hist init_bricks H) :=
  by
  intro g t H
  rw [Strategy_legal, PickUpBricks] at f_law s_law
  specialize f_law t
  specialize s_law t
  dsimp at f_law s_law
  split at f_law
  · rename_i zero
    dsimp [H]
    rw [zero, f_law]
    rw [zero] at s_law
    dsimp at s_law
    rw [s_law]
    decide
  · rename_i one
    dsimp [H]
    rw [one, f_law]
    rw [one] at s_law
    dsimp at s_law
    rw [s_law]
    decide
  · rename_i noZero noOne
    constructor
    · have : 2 ≤ bricks_start_turn_from_ini_hist init_bricks H :=
        by
        rw [Nat.two_le_iff]
        exact ⟨noZero,noOne⟩
      cases' f_law with c c <;> {rw [c] ; linarith}
    · split at s_law
      · rename_i zero
        rw [zero, s_law]
      · rename_i one
        rw [one, s_law]
      · have : 2 ≤ bricks_start_turn_from_ini_hist init_bricks H :=
          by
          rw [Nat.two_le_iff]
          exact ⟨noZero,noOne⟩
        cases' s_law with c c <;> {rw [c] ; linarith}

lemma acts_pos_condition
  (f_strat s_strat : Strategy ℕ ℕ)
  (f_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat s_strat) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             fst_lawful := f_law
                             snd_strat := s_strat
                             snd_lawful := s_law } ;
   ∀ turn : ℕ,
  let S := g.state_on_turn ;
  let H := History_on_turn init_bricks f_strat s_strat turn ;
  S (turn + 1) ≠ 0 → (f_strat init_bricks H ≠ 0 ∧ s_strat init_bricks H ≠ 0) :=
  by
  intro g t S H Snz
  rw [Strategy_legal, PickUpBricks] at f_law s_law
  specialize f_law t
  specialize s_law t
  dsimp at f_law s_law
  split at f_law
  · rename_i zero
    exfalso
    apply Snz
    dsimp [S]
    have fact : g.toSymm_Game_World = PickUpBricks init_bricks := by rfl
    rw [← PUB_state_bricks fact (t + 1)]
    rw [bricks_start_turn_from_ini_hist] at zero
    rw [History_on_turn]
    split_ifs
    all_goals rw [bricks_start_turn_from_ini_hist] ; dsimp ; rw [List.sum_cons , add_comm, ← Nat.sub_sub, zero, Nat.zero_sub]
  · rename_i one
    rw [one] at s_law
    dsimp at s_law
    rw [f_law,s_law]
    decide
  · rename_i noZ noO
    constructor
    · cases' f_law with c c <;> {rw [c] ; decide}
    · split at s_law
      · rename_i no ; exfalso ; exact noZ no
      · rename_i no ; exfalso ; exact noO no
      · cases' s_law with c c <;> {rw [c] ; decide}


lemma termination_pre
  (f_strat s_strat : Strategy ℕ ℕ)
  (f_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat s_strat) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             fst_lawful := f_law
                             snd_strat := s_strat
                             snd_lawful := s_law } ;
  ∀ turn : ℕ, (g.state_on_turn (turn+1) < g.state_on_turn turn)
                  ∨ (g.state_on_turn  (turn + 1) = 0) :=
  by
  intro g turn
  rw [or_iff_not_imp_right]
  intro non_zero
  by_cases q : Turn_fst (turn + 1)
  · rw [g.state_on_turn_fst_to_snd turn q]
    have : g.toSymm_Game_World = PickUpBricks init_bricks := by rfl
    rw [← PUB_state_bricks this turn]
    dsimp [g, PickUpBricks]
    rw [bricks_start_end]
    apply Nat.sub_lt_self
    · rw [Nat.pos_iff_ne_zero]
      have := acts_pos_condition init_bricks f_strat s_strat f_law s_law turn non_zero
      exact this.1
    · have := acts_le_bricks init_bricks f_strat s_strat f_law s_law turn
      exact this.1
  · rw [g.state_on_turn_snd_to_fst turn q]
    have : g.toSymm_Game_World = PickUpBricks init_bricks := by rfl
    rw [← PUB_state_bricks this turn]
    dsimp [g, PickUpBricks]
    rw [bricks_start_end]
    apply Nat.sub_lt_self
    · rw [Nat.pos_iff_ne_zero]
      have := acts_pos_condition init_bricks f_strat s_strat f_law s_law turn non_zero
      exact this.2
    · have := acts_le_bricks init_bricks f_strat s_strat f_law s_law turn
      exact this.2



lemma termination
  (fst_strat snd_strat : Strategy ℕ ℕ )
  (f_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat f_strat)
  (s_law : Strategy_legal init_bricks (fun _ : ℕ => (PickUpBricks init_bricks).law) f_strat s_strat s_strat) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             fst_lawful := f_law
                             snd_strat := s_strat
                             snd_lawful := s_law } ;
  ∃ turn : ℕ,  g.state_on_turn turn = 0
  :=
  by
  intro g
  apply Nat.well_ordered
  apply termination_pre



theorem Main_Thm
  (win_hyp : init_bricks % 3 = 1 ∨ init_bricks % 3 = 2) :
  (PickUpBricks init_bricks).is_fst_win :=
  by
  use pub_win_strat
  intro s_strat
  use (pub_win_strat_legal init_bricks s_strat)
  intro s_law
  have wf : _ := Nat.lt_wfRel.wf
  rw [WellFounded.wellFounded_iff_has_min] at wf
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := pub_win_strat
                             fst_lawful := pub_win_strat_legal init_bricks s_strat
                             snd_strat := s_strat
                             snd_lawful := s_law }
  specialize wf (fun x : ℕ => g.state_on_turn x = 0)
  specialize wf (termination init_bricks pub_win_strat s_strat (pub_win_strat_legal init_bricks s_strat) s_law)
  obtain ⟨end_turn, end_turn_z, end_turn_prop⟩ := wf
  use end_turn
  constructor
  · sorry
  · constructor
    · dsimp [PickUpBricks]
      exact end_turn_z
    · intro t t_lt_end
      rw [Symm_Game.state_on_turn_neutral]
      split_ifs
      all_goals dsimp [PickUpBricks]
      all_goals intro con
      all_goals apply end_turn_prop t con
      all_goals exact t_lt_end




#exit

def pick_up_bricks_history (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ) : ℕ → List ℕ
| 0 => []
| (turn + 1) => if (turn % 2 = 0)
                then ((fst_strat bricks (pick_up_bricks_history bricks fst_strat  snd_strat turn)) :: (pick_up_bricks_history bricks fst_strat  snd_strat turn))
                else ((snd_strat bricks (pick_up_bricks_history bricks fst_strat  snd_strat turn)) :: (pick_up_bricks_history bricks fst_strat  snd_strat turn))


def numerology_strat (bricks : ℕ) (history : List ℕ) :=
 if ((Nat.Prime (List.length history)) ∧ ((bricks + (List.headD history 0)) % 2 = 1))
 then 2
 else 1

def win_strat (bricks : ℕ) (history : List ℕ) :=
  if ((bricks - history.sum ) % 3) = 1 then 1 else 2

def pick_up_bricks_state (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ) (turn : ℕ) :=
  bricks - (pick_up_bricks_history bricks fst_strat snd_strat turn).sum

def pick_up_bricks_state_history (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ) (turn : ℕ) :=
 List.map (fun t => pick_up_bricks_state bricks fst_strat snd_strat t) (List.range (turn + 1))

#eval pick_up_bricks_state_history 10 numerology_strat numerology_strat 5
#eval pick_up_bricks_state_history 10 numerology_strat numerology_strat 10
#eval pick_up_bricks_state_history 10 numerology_strat numerology_strat 20

#eval pick_up_bricks_state_history 10 win_strat numerology_strat 5
#eval pick_up_bricks_state_history 10 win_strat numerology_strat 10
#eval pick_up_bricks_state_history 10 win_strat numerology_strat 20

def strat_stealing_strat (bricks : ℕ) (history : List ℕ) :=
  List.headD history 1

#eval pick_up_bricks_state_history 20 win_strat strat_stealing_strat 5
#eval pick_up_bricks_state_history 20 win_strat strat_stealing_strat 10
#eval pick_up_bricks_state_history 20 win_strat strat_stealing_strat 20

#eval pick_up_bricks_history 20 win_strat strat_stealing_strat 20
  -- history of actions: note that the odd actions are always equal to the prevous action
  -- that's startegy stealing


def legal_strat (strat :  ℕ → (List ℕ) → ℕ) : Prop :=
  ∀ bricks : ℕ, ∀ history : List ℕ, ((strat bricks history = 1 ) ∨ (strat bricks history = 2))
  -- tecnically on should check that there are enough bricks to pick up
  -- but with subtraction on nat, this trns out to be fine
  -- Note: the current number of bricks is (bricks - history.sum)
  -- Adding bricks as parameter would complicate things in the inductions to come.



lemma termination_pre (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ)
                      (hf : legal_strat fst_strat) (hs : legal_strat snd_strat):
      ∀ turn : ℕ, (pick_up_bricks_state bricks fst_strat snd_strat (turn+1) < pick_up_bricks_state bricks fst_strat snd_strat turn)
                  ∨ (pick_up_bricks_state bricks fst_strat snd_strat (turn + 1) = 0) :=
  by
  intro turn
  rw [or_iff_not_imp_right]
  intro non_zero
  simp [pick_up_bricks_state, pick_up_bricks_history] at *
  simp [legal_strat] at hf
  simp [legal_strat] at hs
  specialize hf bricks (pick_up_bricks_history bricks fst_strat snd_strat turn)
  specialize hs bricks (pick_up_bricks_history bricks fst_strat snd_strat turn)
  split_ifs with h
  · simp
    cases' hf with hf hf
    · rw [hf]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_pos h] at non_zero
      simp at non_zero
      rw [hf] at non_zero
      linarith
    · rw [hf]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_pos h] at non_zero
      simp at non_zero
      rw [hf] at non_zero
      linarith
  · simp
    cases' hs with hs hs
    · rw [hs]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_neg h] at non_zero
      simp at non_zero
      rw [hs] at non_zero
      linarith
    · rw [hs]
      rw [tsub_lt_tsub_iff_left_of_le]
      linarith
      rw [add_comm]
      rw [← Nat.lt_iff_add_one_le]
      rw [if_neg h] at non_zero
      simp at non_zero
      rw [hs] at non_zero
      linarith





lemma termination (bricks : ℕ) (fst_strat snd_strat : ℕ → (List ℕ) → ℕ)
                  (hf : legal_strat fst_strat) (hs : legal_strat snd_strat):
      ∃ turn : ℕ,  pick_up_bricks_state bricks fst_strat snd_strat turn = 0
      :=
  by
  apply Nat.well_ordered
  intro n
  rw [or_iff_not_imp_right]
  intro nz
  simp [pick_up_bricks_state, pick_up_bricks_history] at nz
  dsimp [legal_strat] at hf
  dsimp [legal_strat] at hs
  simp [pick_up_bricks_state, pick_up_bricks_history]
  specialize hf bricks (pick_up_bricks_history bricks fst_strat snd_strat n)
  specialize hs bricks (pick_up_bricks_history bricks fst_strat snd_strat n)
  rw [tsub_lt_tsub_iff_left_of_le]
  split_ifs with h
  · rw [List.sum_cons]
    cases' hf with hf hf
    · linarith
    · linarith
  · rw [List.sum_cons]
    cases' hs with hs hs
    · linarith
    · linarith
  apply le_of_lt
  exact nz

lemma win_strat_legal : legal_strat win_strat :=
  by
  dsimp [legal_strat]
  intro b h
  dsimp [win_strat]
  split_ifs with H
  left
  rfl
  right
  rfl
