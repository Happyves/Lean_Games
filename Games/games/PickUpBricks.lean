/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.HistoryAPI



variable (init_bricks : ℕ) -- the initial number of bricks as a variable

/--
Given an initial number of bricks and a history of bricks taken, return the current number of bricks.
-/
def bricks_from_ini_hist (ini : ℕ) (hist : List ℕ) := ini - hist.sum

/--
Given an initial number of bricks, a history of bricks taken and the current number of bricks
being taken, return the current number of bricks.
-/
def bricks_from_ini_hist_act (ini : ℕ) (hist : List ℕ) (act : ℕ) := ini - hist.sum - act


lemma bricks_cons (ini : ℕ) (hist : List ℕ) (x : ℕ) :
  bricks_from_ini_hist ini (x :: hist) = bricks_from_ini_hist ini hist - x :=
  by
  dsimp [bricks_from_ini_hist]
  rw [List.sum_cons]
  rw [add_comm, Nat.sub_add_eq]

/--
The game of "pick-up-bricks" is played by either player pick 1 or 2 bricks
from a stack of bricks. The player that picks the last brick wins.
-/
def PickUpBricks : Symm_Game_World ℕ ℕ where
  init_game_state := init_bricks
  fst_win_states := (fun hist => Turn_fst hist.length ∧ bricks_from_ini_hist init_bricks hist = 0) -- won once no bricks left
  snd_win_states := (fun hist => Turn_snd hist.length ∧ bricks_from_ini_hist init_bricks hist = 0)
  transition :=  bricks_from_ini_hist_act init_bricks
  law := fun _ act =>  act = 1 ∨ act = 2



instance : DecidablePred (PickUpBricks init_bricks).fst_win_states := by
  intro hist
  dsimp [PickUpBricks, bricks_from_ini_hist]
  exact And.decidable

instance : DecidablePred (PickUpBricks init_bricks).snd_win_states := by
  intro hist
  dsimp [PickUpBricks, bricks_from_ini_hist]
  exact And.decidable


/-- The (to be proven) winning strategy for the second player -/
def pub_win_strat : (PickUpBricks init_bricks).sStrategy :=
  fun hist _ _ =>
    match con : hist with
    | [] => False.elim (by contradiction)
    | last :: _ =>
        if last = 2
        then ⟨1, (by dsimp [PickUpBricks] ; left ; rfl)⟩
        else ⟨2, (by dsimp [PickUpBricks] ; right ; rfl)⟩

/-- Some toy strategy for ilustrative purposes -/
def toy_strat : (PickUpBricks init_bricks).fStrategy :=
  fun hist _ _ => ⟨1, (by dsimp [PickUpBricks] ; left ; rfl)⟩



/--
Pick up bricks played with 37 initial bricks, with the winning strat as
first strat and the toy strat as second strat.
-/
def PickUpBricks_pubWin_vs_toy : Symm_Game ℕ ℕ :=
  {(PickUpBricks 37) with
   fst_strat := toy_strat 37
   snd_strat := pub_win_strat 37
  }


instance : DecidablePred (PickUpBricks_pubWin_vs_toy).fst_win_states := by
  intro hist
  dsimp [PickUpBricks_pubWin_vs_toy]
  apply instDecidablePredListNatFst_win_statesPickUpBricks

instance : DecidablePred (PickUpBricks_pubWin_vs_toy).snd_win_states := by
  intro hist
  dsimp [PickUpBricks_pubWin_vs_toy]
  apply instDecidablePredListNatSnd_win_statesPickUpBricks

-- The moves of the players, turn by turn, up to turn 30
#eval (PickUpBricks_pubWin_vs_toy.hist_on_turn 30).val.reverse

--The state of the game, turn by turn, up to turn 30
#eval (List.range 30).map (PickUpBricks_pubWin_vs_toy.state_on_turn)


lemma trick
  (f_strat : (PickUpBricks init_bricks).fStrategy)
  (t : Nat) (T : Turn_snd t) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             snd_strat := pub_win_strat init_bricks
                            } ;
  let f := g.fst_strat (g.hist_on_turn t).val (by rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn_length, ← Turn_snd_fst_step] ; exact T) (g.hist_on_turn t).prop.1
  let s := g.snd_strat (g.hist_on_turn (t+1)).val (by rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn_length, ← Turn_snd_step] ; exact T) (g.hist_on_turn (t+1)).prop.1
  s.val + f.val = 3 :=
  by
  intro g f s
  cases' f.prop with one two
  · have : s.val = 2 :=
      by
      dsimp [s, pub_win_strat]
      split
      · contradiction
      · rename_i last tail _ _ _ _ main _ _
        have := Symm_Game_World.hist_on_turn_snd_to_fst g.toSymm_Game_World g.fst_strat g.snd_strat t T
        simp_rw [Symm_Game.hist_on_turn] at main
        dsimp [g] at this
        rw [main] at this -- most painful rewrite ever
        replace this := List.head_eq_of_cons_eq this
        dsimp [f] at one
        simp_rw [Symm_Game.hist_on_turn] at one
        simp_rw [one] at this
        rw [if_neg (by rw [this] ; decide)]
    rw [one, this]
  · have : s.val = 1 :=
      by
      dsimp [s, pub_win_strat]
      split
      · contradiction
      · rename_i last tail _ _ _ _ main _ _
        have := Symm_Game_World.hist_on_turn_snd_to_fst g.toSymm_Game_World g.fst_strat g.snd_strat t T
        simp_rw [Symm_Game.hist_on_turn] at main
        dsimp [g] at this
        rw [main] at this
        replace this := List.head_eq_of_cons_eq this
        dsimp [f] at two
        simp_rw [Symm_Game.hist_on_turn] at two
        simp_rw [two] at this
        rw [if_pos (by rw [this])]
    rw [two, this]



-- to generalize, and to mathlib
lemma List.sum_le_sum_of_suffix (h H : List Nat) (suf : h <:+ H) :
  h.sum ≤ H.sum :=
  by
  obtain ⟨l,ldef⟩ := suf
  rw [← ldef, List.sum_append]
  exact Nat.le_add_left (sum h) (sum l)



lemma bricks_zero_stay_zero_suf (h H : List Nat) (suf : h <:+ H)
  (main : bricks_from_ini_hist init_bricks h = 0) :
  bricks_from_ini_hist init_bricks H = 0 :=
  by
  dsimp [bricks_from_ini_hist] at *
  rw [← Nat.le_zero, ← main]
  apply tsub_le_tsub (le_refl _) (List.sum_le_sum_of_suffix h H suf)



lemma bricks_zero_stay_zero
  (f_strat : (PickUpBricks init_bricks).fStrategy) (t n : Nat):
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             snd_strat := pub_win_strat init_bricks
                            } ;
  bricks_from_ini_hist init_bricks (g.hist_on_turn t) = 0 →
    bricks_from_ini_hist init_bricks (g.hist_on_turn (t+n)) = 0 :=
  by
  intro g main
  apply bricks_zero_stay_zero_suf _ _ _ _ main
  apply Symm_Game_World.hist_on_turn_suffix
  exact Nat.le_add_right t n




lemma loop_invariant
  (win_hyp : 3 ∣ init_bricks)
  (f_strat : (PickUpBricks init_bricks).fStrategy) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             snd_strat := pub_win_strat init_bricks
                            } ;
  ∀ turn, Turn_snd turn → 3 ∣ bricks_from_ini_hist init_bricks (g.hist_on_turn turn) :=
  by
  intro g t T
  apply Invariant_snd _ _ t T
  · dsimp [bricks_from_ini_hist, Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
    exact win_hyp
  · intro t T ih
    by_cases Q : bricks_from_ini_hist init_bricks (g.hist_on_turn t) = 0
    · rw [bricks_zero_stay_zero _ _ _ 2 Q]
      exact Nat.dvd_zero 3
    · simp_rw [← Nat.pos_iff_ne_zero] at Q
      rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn_2step_snd _ _ _ T, bricks_from_ini_hist]
      rw [List.sum_cons, List.sum_cons, ← Nat.add_assoc]
      have := trick init_bricks f_strat t T
      simp_rw [Symm_Game.hist_on_turn] at this
      rw [this]
      clear this
      rw [Nat.add_comm, ← tsub_tsub]
      apply Nat.dvd_sub
      · apply Nat.le_of_dvd Q ih
      · apply ih
      · exact Nat.dvd_refl 3


lemma bricks_decrease
  (f_strat : (PickUpBricks init_bricks).fStrategy) (t: Nat):
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             snd_strat := pub_win_strat init_bricks
                            } ;
  bricks_from_ini_hist init_bricks (g.hist_on_turn t) ≠ 0 →
  bricks_from_ini_hist init_bricks (g.hist_on_turn (t+1)) < bricks_from_ini_hist init_bricks (g.hist_on_turn t) :=
  by
  intro g main
  dsimp [bricks_from_ini_hist]
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_sub_ne_zero main
  · dsimp [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
    split_ifs with T
    · rw [List.sum_cons]
      have := (f_strat (g.hist_on_turn t).val (by rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn_length] ; exact T) (g.hist_on_turn t).prop.1).prop
      cases' this with q q
      · apply Nat.lt_add_of_pos_left
        simp_rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn] at q
        simp_rw [q]
        decide
      · apply Nat.lt_add_of_pos_left
        simp_rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn] at q
        simp_rw [q]
        decide
    · rw [List.sum_cons]
      have := ((pub_win_strat init_bricks) (g.hist_on_turn t).val (by rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn_length] ; exact T) (g.hist_on_turn t).prop.1).prop
      cases' this with q q
      · apply Nat.lt_add_of_pos_left
        simp_rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn] at q
        simp_rw [q]
        decide
      · apply Nat.lt_add_of_pos_left
        simp_rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn] at q
        simp_rw [q]
        decide


#check Nat.lt_add_of_pos_left


lemma bricks_head_val_of_zero_cons {h : List Nat} {x : Nat}
  (Z : bricks_from_ini_hist init_bricks (x :: h) = 0)
  (NZ : bricks_from_ini_hist init_bricks h ≠ 0)
  (leg : (PickUpBricks init_bricks).hist_legal (x :: h)):
  (bricks_from_ini_hist init_bricks (h)) = 1 ∨ (bricks_from_ini_hist init_bricks ( h)) = 2 :=
  by
  dsimp [Symm_Game_World.hist_legal] at leg
  cases' leg
  rename_i _ now
  dsimp [PickUpBricks] at now
  rw [ite_self] at now
  dsimp [bricks_from_ini_hist] at *
  rw [List.sum_cons, Nat.add_comm, ← tsub_tsub, Nat.sub_eq_zero_iff_le] at Z
  cases' now with one two
  · rw [one] at Z
    interval_cases (init_bricks - List.sum h)
    · contradiction
    · left ; rfl
  · rw [two] at Z
    interval_cases (init_bricks - List.sum h)
    · contradiction
    · left ; rfl
    · right ; rfl


#check Nat.sub_eq_zero_iff_le

lemma PUB_terminates
    (f_strat : (PickUpBricks init_bricks).fStrategy) :
  let g : Symm_Game ℕ ℕ := { (PickUpBricks init_bricks) with
                             fst_strat := f_strat
                             snd_strat := pub_win_strat init_bricks
                            } ;
  ∃ t, bricks_from_ini_hist init_bricks (g.hist_on_turn t) = 0
    ∧ ∀ n < t, bricks_from_ini_hist init_bricks (g.hist_on_turn n) ≠ 0 :=
  by
  intro g
  by_cases Z : bricks_from_ini_hist init_bricks (g.hist_on_turn 0) = 0
  · use 0
    constructor
    · exact Z
    · intro _ _
      contradiction
  · let nz := {m | bricks_from_ini_hist init_bricks (g.hist_on_turn m) ≠ 0}
    have nz_ne : Set.Nonempty nz := by use 0 ; apply Z
    let N := WellFounded.min (@wellFounded_lt Nat _ _) nz nz_ne
    have := WellFounded.min_mem (@wellFounded_lt Nat _ _) nz nz_ne



#exit

theorem PUB_snd_win (win_hyp : 3 ∣ init_bricks) :
  (PickUpBricks init_bricks).is_snd_win :=
  by
  use pub_win_strat init_bricks
  intro f_strat
