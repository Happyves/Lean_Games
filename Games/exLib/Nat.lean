/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic


/-- A decreasing function `f : ℕ → ℕ` will eventually reach `0` -/
lemma Nat.well_ordered
  (f : ℕ → ℕ) (H : ∀ n, (f (n+1) < f n) ∨ (f (n+1) = 0)) :
  ∃ n, f n = 0 :=
  by
  have wf : _ := Nat.lt_wfRel.wf
  have l (x : ℕ) : f x ∈ f '' Set.univ :=
    by
    rw [Set.mem_image]
    use x
    constructor
    apply Set.mem_univ
    rfl
  rw [WellFounded.wellFounded_iff_has_min] at wf
  specialize wf (Set.image f Set.univ) _
  · use f 0
    exact l 0
  · rcases wf with ⟨m, mdef, mprop⟩
    rw [Set.mem_image] at mdef
    rcases mdef with ⟨k, _, kprop⟩
    use (k+1)
    by_contra! con
    specialize H k
    rw [or_iff_not_imp_right] at H
    specialize H con
    specialize mprop (f (k+1)) (l (k+1))
    apply mprop
    rw [← kprop]
    apply H



def Nat.induct_2_step {p : ℕ → Prop} (m : ℕ)
  (h0 : p 0) (h1 : p 1) (step : ∀ n, p n → p (n+1) → p (n+2)):
  p m :=
  by
  apply Nat.strong_induction_on
  intro n hn
  cases' n with n
  · apply h0
  · cases' n with n
    · apply h1
    · apply step
      · apply hn
        rw [Nat.succ_eq_add_one]
        linarith
      · apply hn
        rw [Nat.succ_eq_add_one]
        linarith
