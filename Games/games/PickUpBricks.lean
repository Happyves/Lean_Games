/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Termination
import Games.gameLib.HistoryAPI


/-
The game of Pick-Up-Bricks is played by two players with a stack of bricks.
At each round, a player may pick one or two bricks from the stack.
The last player to pick a brick wins the game.

One can show that this game has a wining strategy for the secodn player if
the stack of bricks is divisible by 3. Indeed, if the first players bicks
1 brick, the second may pick 2, and if the first player picks 2 bricks,
then the second player may pick 1. Thus, after each player took their turn,
the stack of bricks will remain divisible by 3, after the second players turn.
This must be the case for the last turn, as `3 ∣ 0`, so that the last turn must
be the second player's, who therefore wins the game.

The key parts of the file are:
- `PickUpBricks` the definition of the game
- `pub_win_strat` defines a startegy that is a winning strategy
  for the second player if the stack of bricks is divisible by 3.
- `trick` and `loop_invariant` which are used to prove that
  Pick-Up-Bricks has a winning strategy for the second player
  if the stack of bricks is divisible by 3.
- `PUB_terminates` is a lemma used to justify that `PickUpBricks` terminates.
- `PUB_snd_win` shows that the game has a winning strategy.


Note that the proofs still need major cleaning.
-/



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
  · let nz := {b | ∃ m, (b = bricks_from_ini_hist init_bricks (g.hist_on_turn m)) ∧ b ≠ 0}
    have nz_ne : Set.Nonempty nz := by use bricks_from_ini_hist init_bricks (g.hist_on_turn 0) ; use 0
    obtain ⟨M,Md,Mz⟩ := WellFounded.min_mem (@wellFounded_lt Nat _ _) nz nz_ne
    use (M+1)
    constructor
    · by_contra con
      apply @WellFounded.not_lt_min _ _ (@wellFounded_lt Nat _ _) nz nz_ne  (bricks_from_ini_hist init_bricks (g.hist_on_turn (M+1))) (by use M+1)
      rw [Md]
      rw [Md] at Mz
      apply bricks_decrease _ _ _ Mz
    · intro n nM
      rw [Nat.lt_succ] at nM
      intro con
      apply Mz
      rw [Md]
      apply bricks_zero_stay_zero_suf _ _ _ _ con
      rw [Symm_Game.hist_on_turn]
      apply Symm_Game_World.hist_on_turn_suffix
      exact nM



lemma help_1 : ¬ 3 ∣ 1 := by decide
lemma help_2 : ¬ 3 ∣ 2 := by decide




theorem PUB_snd_win (win_hyp : 3 ∣ init_bricks) :
  (PickUpBricks init_bricks).is_snd_win :=
  by
  use pub_win_strat init_bricks
  intro f_strat
  obtain ⟨t, bz, bnz⟩ := PUB_terminates init_bricks f_strat
  simp_rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn] at bz bnz
  use t
  constructor
  · dsimp [PickUpBricks]
    constructor
    · cases' t with t
      · dsimp [Game.hist_on_turn, Game_World.hist_on_turn]
        decide
      · by_contra con
        simp_rw [Game.hist_on_turn, Game_World.hist_on_turn_length] at con
        simp_rw [Turn_not_snd_iff_fst, ← Turn_snd_fst_step] at con
        have := Game_World.hist_on_turn_snd_to_fst (PickUpBricks init_bricks).toGame_World f_strat (pub_win_strat init_bricks) t con
        dsimp [PickUpBricks] at this
        simp_rw [← Nat.succ_eq_add_one] at this
        simp_rw [Symm_Game_World.hist_legal] at bnz
        let H := (Game_World.hist_on_turn (PickUpBricks init_bricks).toGame_World f_strat (pub_win_strat init_bricks) t)
        have pain : bricks_from_ini_hist init_bricks ((f_strat H.val (by rw [Game_World.hist_on_turn_length, ← Turn_snd_fst_step] ; exact con) H.prop.1) :: H) = 0 :=
          by
          convert bz
          convert this.symm
        have pain2 : (f_strat H.val (by rw [Game_World.hist_on_turn_length, ← Turn_snd_fst_step] ; exact con) H.prop.1).val :: H = (Game_World.hist_on_turn (PickUpBricks init_bricks).toGame_World f_strat (pub_win_strat init_bricks) (t+1)) :=
          by
          dsimp [Game_World.hist_on_turn]
          rw [dif_pos (by rw [← Turn_snd_fst_step] ; exact con) ]
        replace con := loop_invariant init_bricks win_hyp f_strat _ con
        have that := bricks_head_val_of_zero_cons _ pain (bnz t (Nat.lt_succ_self t)) (by rw [pain2] ; apply Symm_Game_World.hist_on_turn_legal)
        simp_rw [Symm_Game.hist_on_turn, Symm_Game_World.hist_on_turn] at con
        cases' that with oh no
        · rw [oh] at con
          exact help_1 con
        · rw [no] at con
          exact help_2 con
    · exact bz
  · dsimp [Game.state_on_turn_neutral, Game_World.state_on_turn_neutral]
    intro n nt con
    cases' con with oh no
    · dsimp [PickUpBricks] at oh
      exact bnz n nt oh.2
    · dsimp [PickUpBricks] at no
      exact bnz n nt no.2
