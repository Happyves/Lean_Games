/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic


-- # Turns



/--
Turn of the first player.
Turn 0 represents initial state, then turns represent the state after the action-/
def Turn_fst (turn : ℕ): Prop := turn % 2 = 1

/--
Turn of the decond player.
Turn 0 represents initial state, then turns represent the state after the action-/
def Turn_snd (turn : ℕ): Prop := ¬ (turn % 2 = 1)


instance : DecidablePred Turn_fst :=
  fun turn => by rw [Turn_fst] ; exact Nat.decEq (turn % 2) 1

instance : DecidablePred Turn_snd :=
  fun turn => by rw [Turn_snd] ; exact Not.decidable



lemma Turn_not_fst_iff_snd (turn : ℕ) : (¬ Turn_fst turn) ↔ Turn_snd turn :=
  by rw [Turn_fst, Turn_snd]

lemma Turn_not_snd_iff_fst (turn : ℕ) : (¬ Turn_snd turn) ↔ Turn_fst turn :=
  by rw [Turn_fst, Turn_snd, not_ne_iff]

lemma Turn_snd_iff_not_fst (turn : ℕ) : Turn_snd turn ↔ (¬ Turn_fst turn) :=
  by rw [Turn_fst, Turn_snd]

lemma Turn_fst_iff_not_snd (turn : ℕ) : Turn_fst turn ↔ (¬ Turn_snd turn) :=
  by rw [Turn_fst, Turn_snd, not_ne_iff]

lemma Turn_fst_or_snd (turn : ℕ) : Turn_fst turn ∨ Turn_snd turn :=
  by rw [Turn_fst, Turn_snd] ; apply em


lemma Turn_fst_step (turn : ℕ): Turn_fst turn ↔ Turn_fst (turn + 2) :=
  by
  simp_rw [Turn_fst] at *
  rw [Nat.add_mod]
  norm_num


lemma Turn_snd_step (turn : ℕ): Turn_snd turn ↔ Turn_snd (turn + 2) :=
  by
  rw [← Turn_not_fst_iff_snd, ← Turn_not_fst_iff_snd, @not_iff_not]
  apply Turn_fst_step

lemma Turn_fst_snd_step (turn : ℕ): Turn_fst turn ↔ Turn_snd (turn + 1) :=
  by
  rw [Turn_fst, Turn_snd] at *
  constructor
  · intro h
    rw [Nat.add_mod, h]
    decide
  · intro h
    have := (or_iff_not_imp_right.mp (Nat.mod_two_eq_zero_or_one (turn+1))) h
    rwa [Nat.succ_mod_two_eq_zero_iff] at this


lemma Turn_snd_fst_step (turn : ℕ): Turn_snd turn ↔ Turn_fst (turn + 1) :=
  by
  rw [← Turn_not_fst_iff_snd, ← @Turn_not_snd_iff_fst (turn + 1), @not_iff_not]
  apply Turn_fst_snd_step


lemma Turn_fst_not_step (turn : ℕ): Turn_fst turn ↔ ¬ Turn_fst (turn + 1) :=
  by
  rw [Turn_not_fst_iff_snd]
  apply Turn_fst_snd_step


lemma Turn_snd_not_step (turn : ℕ): Turn_snd turn ↔ ¬ Turn_snd (turn + 1) :=
  by
  rw [Turn_not_snd_iff_fst]
  apply Turn_snd_fst_step


lemma Turn_not_fst_step (turn : ℕ): ¬ Turn_fst turn ↔ Turn_fst (turn + 1) :=
  by
  rw [not_iff_comm, Iff.comm , Turn_fst_not_step]



lemma Turn_not_snd_step (turn : ℕ): ¬ Turn_snd turn ↔  Turn_snd (turn + 1) :=
  by
  rw [not_iff_comm, Iff.comm , Turn_snd_not_step]


lemma Invariant_fst {p : ℕ → Prop}
  (bh : p 1) (ih : ∀ turn : ℕ, Turn_fst turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, Turn_fst turn → p turn :=
  by
  intro t
  apply Nat.twoStepInduction _ _ _ t
  · intro no
    rw [Turn_fst] at no
    contradiction
  · exact (fun _ => bh)
  · intro n a _ c
    rw [← Turn_fst_step] at c
    exact ih n c (a c)


lemma Invariant_snd {p : ℕ → Prop}
  (bh : p 0) (ih : ∀ turn : ℕ, Turn_snd turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, Turn_snd turn → p turn :=
  by
  intro t
  apply Nat.twoStepInduction _ _ _ t
  swap
  · intro no
    rw [Turn_snd] at no
    contradiction
  · exact (fun _ => bh)
  · intro n a _ c
    rw [← Turn_snd_step] at c
    exact ih n c (a c)

lemma Invariant_snd' {p : ℕ → Prop}
  (bh : p 2) (ih : ∀ turn : ℕ, Turn_snd turn → p turn → p (turn + 2)):
  ∀ turn : ℕ, turn ≥ 2 → Turn_snd turn → p turn :=
  by
  intro t
  apply Nat.twoStepInduction _ _ _ t
  swap
  · intro no nope
    rw [Turn_snd] at nope
    contradiction
  · intro no
    norm_num at no
  · intro n a _ b c
    rw [← Turn_snd_step] at c
    cases' n with m
    · apply bh
    · cases' m with k
      · rw [Turn_snd] at c
        contradiction
      · apply ih
        · apply c
        · apply a _ c
          rw [Nat.succ_eq_add_one]
          apply Nat.le_add_left
