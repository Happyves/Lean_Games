/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Stealing



-- # Chomp state lemmata

def domi (p q : ℕ × ℕ) : Prop := p.1 ≤ q.1 ∧ p.2 ≤ q.2

def nondomi (p q : ℕ × ℕ) : Prop := ¬ domi p q

instance : DecidableRel domi :=
  by
  intro p q
  rw [domi]
  exact And.decidable

instance : DecidableRel nondomi :=
  by
  intro p q
  rw [nondomi]
  exact Not.decidable

instance (l : List (ℕ × ℕ)) : DecidablePred (fun p => ∀ q ∈ l, nondomi q p) :=
  by
  intro p
  dsimp [nondomi,domi]
  exact List.decidableBAll (fun x => ¬(x.1 ≤ p.1 ∧ x.2 ≤ p.2)) l


def Chomp_state (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) :=
  ini.filter (fun p => ∀ q ∈ hist, nondomi q p)


lemma Chomp_state_sub (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) :
  Chomp_state ini (l ++ L) ⊆ Chomp_state ini l :=
  by
  intro x xdef
  dsimp [Chomp_state] at *
  rw [Finset.mem_filter] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact List.mem_append.mpr (Or.inl ql)

lemma Chomp_state_sub' (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) :
  Chomp_state ini (l ++ L) ⊆ Chomp_state ini L :=
  by
  intro x xdef
  dsimp [Chomp_state] at *
  rw [Finset.mem_filter] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact List.mem_append_right l ql

-- to mathlib ?!?
lemma List.cons_eq_singleton_append (l : List α) (x : α) : x :: l = [x] ++ l := by exact rfl

lemma Chomp_state_sub_cons (ini : Finset (ℕ × ℕ)) (x : ℕ × ℕ) (l :  List (ℕ × ℕ)) :
  Chomp_state ini (x :: l) ⊆ Chomp_state ini l :=
  by
  rw [List.cons_eq_singleton_append]
  apply Chomp_state_sub'


lemma Chomp_state_sub_of_hist_sub (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) (h : l ⊆ L) :
  Chomp_state ini (L) ⊆ Chomp_state ini l :=
  by
  intro x xdef
  dsimp [Chomp_state] at *
  rw [Finset.mem_filter] at *
  constructor
  · apply xdef.1
  · intro q ql
    apply xdef.2
    exact h ql

-- to mathlib
lemma List.mem_of_suffix  {a b : List α} {x : α} (ha : a <:+ b) (hx : x ∈ a) : x ∈ b := by
  obtain ⟨t,tdef⟩ := ha ; rw [← tdef, List.mem_append] ; right ; exact hx

-- to mathlib
lemma List.subset_of_suffix  {a b : List α} (ha : a <:+ b) : a ⊆ b := by
  intro x xa ; apply List.mem_of_suffix ha xa


lemma Chomp_state_sub_of_hist_suffix (ini : Finset (ℕ × ℕ)) (l L :  List (ℕ × ℕ)) (h : l <:+ L) :
  Chomp_state ini (L) ⊆ Chomp_state ini l :=
  by apply Chomp_state_sub_of_hist_sub ; apply List.subset_of_suffix h



def Chomp_init (height length : ℕ) := (Finset.range (length+1)) ×ˢ (Finset.range (height+1))

lemma Chomp_state_blind (ini : Finset (ℕ × ℕ)) (hist prehist : List (ℕ × ℕ)) :
  Chomp_state (Chomp_state ini prehist) hist = Chomp_state ini (hist ++ prehist) :=
  by
  ext x
  constructor
  · intro H
    dsimp [Chomp_state] at *
    simp_rw [Finset.mem_filter] at *
    constructor
    · exact H.1.1
    · intro q qq
      rw [List.mem_append] at qq
      cases' qq with k k
      · exact H.2 q k
      · exact H.1.2 q k
  · intro H
    dsimp [Chomp_state] at *
    simp_rw [Finset.mem_filter] at *
    constructor
    · constructor
      · exact H.1
      · intro q qh
        apply H.2
        exact List.mem_append_right hist qh
    · intro q qh
      apply H.2
      exact List.mem_append.mpr (Or.inl qh)

lemma Chomp_state_ini_zero (hist : List (ℕ × ℕ)) (hh : (0,0) ∉ hist): Chomp_state {(0,0)} hist = {(0,0)} :=
  by
  dsimp [Chomp_state]
  rw [Finset.filter_eq_self]
  intro x xdef q qh
  rw [Finset.mem_singleton] at xdef
  rw [xdef]
  dsimp [nondomi, domi]
  intro con
  simp_rw [Nat.le_zero] at con
  apply hh
  convert qh
  · exact con.1.symm
  · exact con.2.symm

lemma Chomp_state_has_zero_iff_hist_has_zero
  (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (hist : List (ℕ × ℕ)) :
  (0,0) ∈ Chomp_state ini hist ↔ (0,0) ∉ hist :=
  by
  constructor
  · intro c
    dsimp [Chomp_state] at c
    rw [Finset.mem_filter] at c
    dsimp [nondomi, domi] at c
    intro con
    apply c.2 _ con
    decide
  · intro c
    dsimp [Chomp_state]
    rw [Finset.mem_filter]
    constructor
    · exact hini
    · intro q qh
      dsimp [nondomi, domi]
      intro con
      simp_all only [nonpos_iff_eq_zero]
      unhygienic with_reducible aesop_destruct_products
      simp_all only

lemma Chomp_state_sub_ini (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) :
  Chomp_state ini hist ⊆ ini := by dsimp [Chomp_state]; exact Finset.filter_subset (fun p => ∀ q ∈ hist, nondomi q p) ini

lemma Chomp_state_hist_zero (ini : Finset (ℕ × ℕ) ) (hist : List (ℕ × ℕ)) (main : (0,0) ∈ hist) :
  Chomp_state ini hist = ∅ :=
  by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x xdef
  dsimp [Chomp_state] at xdef
  rw [Finset.mem_filter] at xdef
  apply xdef.2 _ main
  dsimp [domi]
  simp_all only [Prod.forall, zero_le, and_self]


lemma Chomp_state_state_empty (ini : Finset (ℕ × ℕ) ) (hini : (0,0) ∈ ini) (hist : List (ℕ × ℕ)) (main : Chomp_state ini hist = ∅) :
  (0,0) ∈ hist :=
  by
  dsimp [Chomp_state] at main
  simp_rw [Finset.eq_empty_iff_forall_not_mem, Finset.mem_filter] at main
  dsimp [nondomi, domi] at main
  push_neg at main
  specialize main _ hini
  obtain ⟨q, qh, qz1, qz2⟩ := main
  simp only [nonpos_iff_eq_zero] at *
  convert qh <;> {rw [eq_comm] ; assumption}

lemma nondomi_zero (act : ℕ × ℕ) : nondomi act (0,0) ↔ act ≠ (0,0) := by
  dsimp [nondomi,domi]
  simp_rw [Nat.le_zero]
  simp_all only [not_and]
  unhygienic with_reducible aesop_destruct_products
  simp_all only [Prod.mk.injEq, not_and]



lemma Chomp_state_zero_act_non_zero (ini : Finset (ℕ × ℕ)) (hini : (0, 0) ∈ ini) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ)
  (hs : Chomp_state ini hist = {(0,0)}) (ha : act ≠ (0,0)) : Chomp_state ini (act :: hist) = {(0,0)} :=
  by
  dsimp [Chomp_state] at *
  have : (fun p => ∀ q ∈ act :: hist, nondomi q p) = (fun p => (nondomi act p) ∧ (∀ q ∈ hist, nondomi q p)) :=
    by
    ext p
    simp_all only [Prod.forall, List.mem_cons, forall_eq_or_imp]
    unhygienic with_reducible aesop_destruct_products
    simp_all only [Prod.forall, Prod.mk.injEq, not_and]
    apply Iff.intro
    · intro a
      simp_all only [Prod.forall, and_self, true_or, or_true, implies_true, forall_const]
    · intro a a_1 b a_2
      unhygienic with_reducible aesop_destruct_products
      unhygienic aesop_cases a_2
      · simp_all only [Prod.forall]
      · simp_all only [Prod.forall]
  simp_rw [this, Finset.filter_and,hs]
  rw [Finset.inter_eq_right]
  intro y ydef
  rw [Finset.mem_singleton] at ydef
  rw [ydef, Finset.mem_filter]
  exact ⟨ hini, (by rw [nondomi_zero]; exact ha)⟩



lemma Chomp_init_has_zero (height length : ℕ)  : (0,0) ∈ Chomp_init height length :=
  by
  dsimp [Chomp_init]
  simp_rw [Finset.mem_product, Finset.mem_range, and_comm]
  constructor <;> {exact Nat.add_pos_right _ Nat.le.refl}

lemma Chomp_state_ini_not_zero (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0)  : ¬Chomp_state (Chomp_init height length) [] = {(0, 0)} :=
  by
  dsimp [Chomp_state, Chomp_init]
  apply ne_of_not_subset
  intro con
  specialize @con (length, height)
    (by rw [Finset.mem_filter ]
        constructor
        · simp_rw [Finset.mem_product, Finset.mem_range]
          constructor <;> {exact Nat.le.refl}
        · intro q no ; contradiction)
  simp only [Finset.mem_singleton, Prod.mk.injEq] at con
  cases' h with h h
  · exact h con.2
  · exact h con.1


private lemma helper (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) : (0,0) ∉ [(length, height)] :=
  by
  intro con
  rw [List.mem_singleton] at con
  cases' h with h h
  · apply h
    simp_all only [Prod.mk.injEq, ne_eq]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [right, left]
    simp_all only [not_true_eq_false]
  · apply h
    simp_all only [Prod.mk.injEq, ne_eq]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [right, left]
    simp_all only [not_true_eq_false]


lemma Chomp_init_has_len_hei (height length : ℕ) : (length, height) ∈ Chomp_init height length :=
  by
  dsimp [Chomp_init]
  simp_rw [Finset.mem_product, Finset.mem_range]
  constructor
  all_goals {apply Nat.lt_succ_self}

lemma Chomp_state_empty  (ini : (Finset (ℕ × ℕ))) : Chomp_state ini [] = ini :=
  by
  dsimp [Chomp_state]
  rw [Finset.filter_eq_self]
  intro _ _ _ no
  contradiction

lemma Chomp_not_mem_state_of_mem_hist (ini : (Finset (ℕ × ℕ))) (hist : (List (ℕ × ℕ))) (act : ℕ × ℕ) (ha : act ∈ hist) : act ∉ Chomp_state ini hist :=
  by
  dsimp [Chomp_state]
  intro con
  rw [Finset.mem_filter] at con
  replace con := con.2 _ ha
  apply con
  dsimp [domi]
  exact ⟨le_refl act.1, le_refl act.2⟩




-- # Chomp law lemmata

structure Chomp_law (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  act_mem : act ∈ ini
  nd : ∀ q ∈ hist, nondomi q act





-- # Chomp win states lemmata


structure Chomp_win_final (ini : Finset (ℕ × ℕ)) (hist final_h : List (ℕ × ℕ)) (final_a : ℕ × ℕ) : Prop where
  N : Chomp_state ini final_h ≠ ∅
  F : Chomp_state ini (final_a :: final_h) = ∅
  ref : (final_a :: final_h) <:+ hist


def Chomp_win_fst (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) : Prop :=
  ∃ final_h : List (ℕ × ℕ), ∃ final_a : (ℕ × ℕ), Turn_snd (final_h.length + 1) ∧ Chomp_win_final ini hist final_h final_a

def Chomp_win_snd (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) : Prop :=
  ∃ final_h : List (ℕ × ℕ), ∃ final_a : (ℕ × ℕ), Turn_fst (final_h.length + 1) ∧ Chomp_win_final ini hist final_h final_a


lemma Chomp_win_final_ext (ini : Finset (ℕ × ℕ)) (hist final_h : List (ℕ × ℕ)) (final_a act: ℕ × ℕ) :
  Chomp_win_final ini hist final_h final_a → Chomp_win_final ini (act :: hist) final_h final_a := by
  intro main
  constructor
  · exact main.N
  · exact main.F
  · apply List.IsSuffix.trans main.ref
    exact List.suffix_cons act hist

lemma Chomp_win_fst_ext (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act: ℕ × ℕ) :
  Chomp_win_fst ini hist → Chomp_win_fst ini (act :: hist) := by
  rintro ⟨h, a, t, p⟩
  exact ⟨h,a,t, Chomp_win_final_ext ini hist h a act p⟩

lemma Chomp_win_snd_ext (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act: ℕ × ℕ) :
  Chomp_win_snd ini hist → Chomp_win_snd ini (act :: hist) := by
  rintro ⟨h, a, t, p⟩
  exact ⟨h,a,t, Chomp_win_final_ext ini hist h a act p⟩



-- # preChomp


def preChomp (height length : ℕ) : Symm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  init_game_state := Chomp_init height length
  fst_win_states := fun ini hist => Chomp_win_fst ini hist
  snd_win_states := fun ini hist => Chomp_win_snd ini hist
  transition := fun ini hist act => Chomp_state ini (act :: hist)
  law := fun ini hist act =>  if Chomp_state ini hist ≠ ∅
                              then Chomp_law ini hist act
                              else True



-- # Chomp is WL


lemma preChomp_state_sub {height length : ℕ}
  (f_strat : fStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law)
  (s_strat : sStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law) :
  ∀  n,  Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n+1))
    ⊆ Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)) :=
    by
    intro n
    dsimp [History_on_turn]
    split_ifs with T
    · dsimp
      apply Chomp_state_sub_cons
    · dsimp
      apply Chomp_state_sub_cons


lemma preChomp_state_ssub {height length : ℕ}
  (f_strat : fStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law)
  (s_strat : sStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law) :
  ∀  n,  Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)) ≠ ∅ →
    Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n+1))
    ⊂ Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)) :=
    by
    intro n hn
    rw [Finset.ssubset_iff_of_subset (preChomp_state_sub f_strat s_strat n)]
    dsimp [History_on_turn]
    split_ifs with T
    · dsimp
      let act := (f_strat (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)).val (by rw [History_on_turn_length] ; exact T) (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)).prop.1)
      use act.val
      constructor
      · rw [Chomp_state, Finset.mem_filter]
        constructor
        · have := act.prop
          dsimp [preChomp] at this hn
          rw [if_pos hn] at this
          apply this.act_mem
        · have := act.prop
          dsimp [preChomp] at this hn
          rw [if_pos hn] at this
          apply this.nd
      · apply Chomp_not_mem_state_of_mem_hist
        apply List.mem_cons_self
    · dsimp
      let act := (s_strat (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)).val (by rw [History_on_turn_length] ; exact T) (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)).prop.1)
      use act.val
      constructor
      · rw [Chomp_state, Finset.mem_filter]
        constructor
        · have := act.prop
          dsimp [preChomp] at this hn
          rw [if_pos hn] at this
          apply this.act_mem
        · have := act.prop
          dsimp [preChomp] at this hn
          rw [if_pos hn] at this
          apply this.nd
      · apply Chomp_not_mem_state_of_mem_hist
        apply List.mem_cons_self



lemma preChomp_reaches_empty {height length : ℕ}
  (f_strat : fStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law)
  (s_strat : sStrategy (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law) :
  ∃ n, Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n+1)) = ∅ ∧
    ∀ m ≤ n, Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (m)) ≠ ∅ :=
  by
  let states := {s | ∃ n, s = Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n)) ∧ s ≠ ∅}
  have lem : Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat 0).val ≠ ∅ :=
    by
    dsimp only [History_on_turn, Chomp_state, preChomp]
    rw [Finset.filter_true_of_mem]
    · rw [← Finset.nonempty_iff_ne_empty]
      use (length, height)
      apply Chomp_init_has_len_hei height length
    · intro _ _ _ no
      contradiction
  have states_nonempty : Set.Nonempty states := by
    use  Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat 0)
    use 0
    -- wow
    -- constructor
    -- · rfl
    -- · apply lem
  obtain ⟨n,ndef,ne⟩ := WellFounded.min_mem Finset.isWellFounded_ssubset.wf states states_nonempty
  use n
  constructor
  · by_contra con
    apply @WellFounded.not_lt_min _ _ Finset.isWellFounded_ssubset.wf states states_nonempty (Chomp_state (preChomp height length).init_game_state (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat (n+1))) (by use n+1)
    rw [ndef]
    apply preChomp_state_ssub f_strat s_strat n
    rw [← ndef]
    exact ne
  · intro m mln
    contrapose ne
    rw [ndef, not_not, ← Finset.subset_empty]
    rw [not_not] at ne
    rw [← ne]
    apply Chomp_state_sub_of_hist_suffix
    apply History_on_turn_suffix (preChomp height length).toGame_World
    exact mln



lemma preChomp_isWL (height length : ℕ) : (preChomp height length).isWL :=
  by
  intro f_strat s_strat
  obtain ⟨T,Tdef⟩ := preChomp_reaches_empty f_strat s_strat
  use (T+1)
  by_cases Tt : Turn_fst (T+1)
  · apply Game_World.Turn_isWL.ws
    dsimp [preChomp, Chomp_win_snd]
    use (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat T)
    use f_strat (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat T).val (by rw [History_on_turn_length] ; exact Tt) (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat T).prop.1
    constructor
    · rw [History_on_turn_length] ; exact Tt
    · constructor
      · apply Tdef.2
        apply le_refl
      · convert Tdef.1
        dsimp [History_on_turn]
        rw [dif_pos Tt]
      · dsimp [History_on_turn]
        rw [dif_pos Tt]
        apply List.suffix_refl
  · apply Game_World.Turn_isWL.wf
    dsimp [preChomp, Chomp_win_snd]
    use (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat T)
    use s_strat (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat T).val (by rw [History_on_turn_length] ; exact Tt) (History_on_turn (preChomp height length).init_game_state (preChomp height length).law (preChomp height length).law f_strat s_strat T).prop.1
    constructor
    · rw [History_on_turn_length] ; exact Tt
    · constructor
      · apply Tdef.2
        apply le_refl
      · convert Tdef.1
        dsimp [History_on_turn]
        rw [dif_neg Tt]
      · dsimp [History_on_turn]
        rw [dif_neg Tt]
        apply List.suffix_refl





-- # Chomp is playable


lemma preChomp_playable (height length : ℕ) : (preChomp height length).playable :=
  by
  intro h _
  constructor
  · intro _
    by_cases q : Chomp_state (Chomp_init height length) h ≠ ∅
    · dsimp [preChomp]
      simp_rw [if_pos q]
      use (0,0)
      constructor
      · apply Chomp_init_has_zero
      · intro x xh
        rw [nondomi_zero]
        intro con
        apply q
        apply Chomp_state_hist_zero
        rw [con] at xh
        exact xh
    · dsimp [preChomp]
      simp_rw [if_neg q]
      use (0,0)
  · intro _
    by_cases q : Chomp_state (Chomp_init height length) h ≠ ∅
    · dsimp [preChomp]
      simp_rw [if_pos q]
      use (0,0)
      constructor
      · apply Chomp_init_has_zero
      · intro x xh
        rw [nondomi_zero]
        intro con
        apply q
        apply Chomp_state_hist_zero
        rw [con] at xh
        exact xh
    · dsimp [preChomp]
      simp_rw [if_neg q]
      use (0,0)




-- # Chomp has a coherent end


-- to mathlib
lemma List.suffix_same {a b c : List α} (ha : a <:+ c) (hb : b <:+ c) : a <:+ b ∨ b <:+ a := by
  induction' c with x l ih
  · rw [List.suffix_nil] at ha hb
    rw [ha,hb]
    simp only [suffix_nil, or_self]
  · rw [List.suffix_cons_iff] at ha hb
    cases' ha with ha ha
    · cases' hb with hb hb
      · rw [ha,hb]
        left
        exact suffix_rfl
      · rw [ha]
        right
        apply IsSuffix.trans hb
        apply List.suffix_cons
    · cases' hb with hb hb
      · rw [hb]
        left
        apply IsSuffix.trans ha
        apply List.suffix_cons
      · exact ih ha hb


lemma preChomp_coherent_end (height length : ℕ) : (preChomp height length).coherent_end :=
  by
  constructor
  · intro h _ con
    dsimp [preChomp, Chomp_win_fst, Chomp_win_snd] at con
    obtain ⟨fhs,fas,ts,ws⟩ := con.1
    obtain ⟨fhf,faf,tf,wf⟩ := con.2
    cases' List.suffix_same ws.ref wf.ref with q q
    · rw [List.suffix_cons_iff] at q
      cases' q with q q
      · replace q := congrArg List.length q
        simp_rw [List.length_cons, Nat.succ_inj] at q
        rw [← q, Turn_fst_iff_not_snd] at tf
        exact tf ts
      · have := Chomp_state_sub_of_hist_suffix (Chomp_init height length) _ _ q
        rw [ws.F, Finset.subset_empty] at this
        exact wf.N this
    · rw [List.suffix_cons_iff] at q
      cases' q with q q
      · replace q := congrArg List.length q
        simp_rw [List.length_cons, Nat.succ_inj] at q
        rw [← q, Turn_snd_iff_not_fst] at ts
        exact ts tf
      · have := Chomp_state_sub_of_hist_suffix (Chomp_init height length) _ _ q
        rw [wf.F, Finset.subset_empty] at this
        exact ws.N this
  · intro h _ ws act _
    apply Chomp_win_fst_ext
    dsimp [preChomp] at ws
    exact ws
  · intro h _ ws act _
    apply Chomp_win_snd_ext
    dsimp [preChomp] at ws
    exact ws


-- # Chomp

def Chomp (height length : ℕ) : zSymm_Game_World (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  toSymm_Game_World := preChomp height length
  hgw := preChomp_isWL height length
  hgp := preChomp_playable height length
  hgn := preChomp_coherent_end height length




-- # Bait


lemma Chomp_state_empty_not_empty (height length : ℕ) : ¬Chomp_state (Chomp_init height length) [] = ∅ :=
  by rw [Chomp_state_empty] ; rw [← ne_eq ,← Finset.nonempty_iff_ne_empty] ; use (length, height) ; apply Chomp_init_has_len_hei

lemma Bait_leg_fst (height length : ℕ) : (Chomp height length).law (Chomp height length).init_game_state [] (length, height) :=
  by
  dsimp [Chomp, preChomp]
  rw [if_pos (by apply Chomp_state_empty_not_empty)]
  constructor
  · apply Chomp_init_has_len_hei
  · intro _ no
    contradiction

lemma Bait_leg_imp (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) :
  ∀ hist, ∀ act, Hist_legal (Chomp height length).init_game_state (Chomp height length).law (Chomp height length).law (hist) →
    (Chomp height length).law (Chomp height length).init_game_state (hist ++ [(length, height)]) act → (Chomp height length).law (Chomp height length).init_game_state (hist) act :=
  by
  intro hist act _ leg
  dsimp [Chomp, preChomp]
  dsimp [Chomp, preChomp] at leg
  split_ifs with S
  rw [if_pos] at leg
  · constructor
    · exact leg.act_mem
    · intro q qh
      exact leg.nd q (by apply List.mem_append_left ; exact qh)
  · contrapose! S
    apply Chomp_state_hist_zero
    replace S := Chomp_state_state_empty _ (by apply Chomp_init_has_zero) _ S
    rw [List.mem_append] at S
    cases' S with S S
    · exact S
    · exfalso
      apply helper _ _ h
      exact S


lemma nondomi_len_hei {height length : ℕ} (a b : Nat × Nat)
  (adef : a ∈ Chomp_init height length) (bdef : b ∈ Chomp_init height length)
  (main : nondomi b a) : nondomi (length, height) a :=
  by
  dsimp [nondomi, domi]
  dsimp [nondomi, domi] at main
  contrapose! main
  simp_rw [Chomp_init, Finset.mem_product, Finset.mem_range, Nat.lt_succ] at adef bdef
  convert bdef
  · exact le_antisymm adef.1 main.1
  · exact le_antisymm adef.2 main.2

lemma Bait_leg_imp' (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) :
  ∀ hist, ∀ act, Hist_legal (Chomp height length).init_game_state (Chomp height length).law (Chomp height length).law (hist) →
    (Z : ¬ hist = []) → hist.getLast Z = (length, height) → Turn_fst (hist.length + 1) → (Chomp height length).law (Chomp height length).init_game_state hist.dropLast act → (Chomp height length).law (Chomp height length).init_game_state hist act :=
  by
  intro hist act hist_leg Z L T leg
  dsimp [Chomp, preChomp]
  dsimp [Chomp, preChomp] at leg
  split_ifs with S
  rw [← List.dropLast_append_getLast Z, L]
  rw [← List.dropLast_append_getLast Z, L] at S
  rw [if_pos] at leg
  · constructor
    · exact leg.act_mem
    · intro q qh
      rw [List.mem_append] at qh
      cases' qh with qh qh
      · exact leg.nd _ qh
      · match hist with
        | [] => contradiction
        | [_] => dsimp at T ; contradiction
        | x :: y :: l =>
            rw [List.dropLast_cons_of_ne_nil (List.noConfusion)] at leg
            cases' hist_leg
            rename_i _ now
            rw [ite_self] at now
            dsimp [Chomp, preChomp] at now
            rw [if_pos] at now
            · replace now := now.act_mem
              have amem := leg.act_mem
              replace leg := leg.nd x (by apply List.mem_cons_self)
              rw [List.mem_singleton] at qh
              rw [qh]
              apply nondomi_len_hei _ x amem now leg
            · contrapose! S
              apply Chomp_state_hist_zero
              replace S := Chomp_state_state_empty _ (by apply Chomp_init_has_zero) _ S
              rw [List.dropLast_cons_of_ne_nil (List.noConfusion)]
              apply List.mem_append_left
              apply List.mem_cons_of_mem
              have : l ≠ [] := by
                intro con
                simp_rw [con] at L S
                dsimp [List.getLast] at L
                rw [L] at S
                apply helper  _ _ h S
              rw [List.dropLast_cons_of_ne_nil this]
              rw [← List.dropLast_append_getLast this, ← List.cons_append, List.mem_append] at S
              cases' S with S S
              · exact S
              · exfalso
                rw [List.getLast_cons (List.noConfusion)] at L
                rw [List.getLast_cons this] at L
                rw [L] at S
                apply helper  _ _ h S
  · contrapose! S
    apply Chomp_state_hist_zero
    replace S := Chomp_state_state_empty _ (by apply Chomp_init_has_zero) _ S
    exact List.mem_append_left [(length, height)] S







#check Chomp_init_has_len_hei
#check Chomp_state_empty
#check Chomp_state_hist_zero
#check Chomp_state_state_empty
#check Chomp_init_has_zero
#check Chomp_state_sub

#exit

-- Original stuff



noncomputable
def stolen_strat
  (trap : β) (ws : Strategy α β) : Strategy α β :=
  fun ini hist =>
    if hist = []
    then ws ini [trap]
    else ws ini (hist.dropLast ++ [ws ini [trap] , trap])


noncomputable
def pre_stolen_strat
  (trap : β) (s_strat : Strategy α β) : Strategy α β :=
  fun ini hist =>
    if hist = []
    then trap
    else s_strat ini (hist.dropLast)



lemma History_on_turn_stolen_getLast (ini : α)
  (trap : β) (ws s_strat : Strategy α β) (t : ℕ) :
  (History_on_turn ini (stolen_strat trap ws) s_strat (t+1)).getLast (by apply History_on_turn_nonempty_of_succ) = ws ini [trap] :=
  by
  induction' t with t ih
  · dsimp!
    unfold stolen_strat
    rw [if_pos (by rfl)]
  · dsimp [History_on_turn] at *
    by_cases q : Turn_fst (Nat.succ t + 1)
    · simp_rw [if_pos q]
      rw [List.getLast_cons, ih]
    · simp_rw [if_neg q]
      rw [List.getLast_cons, ih]


lemma History_on_turn_stolen_pre_stolen (ini : α)
  (trap : β) (ws s_strat : Strategy α β) (t : ℕ) :
  (History_on_turn ini (stolen_strat trap ws) s_strat t) ++ [trap] =
  History_on_turn ini (pre_stolen_strat trap s_strat) ws (t+1) :=
  by
  induction' t with t ih
  · dsimp [History_on_turn, stolen_strat, pre_stolen_strat]
    rw [if_pos (by decide), if_pos (by rfl)]
  · dsimp [History_on_turn]
    by_cases q : Turn_fst (t + 1)
    · simp_rw [if_pos q]
      rw [Turn_fst_not_step] at q
      rw [if_neg q]
      rw [List.cons_append, ih]
      dsimp [History_on_turn]
      rw [← Turn_fst_not_step] at q
      rw [if_pos q]
      congr
      cases' t with t
      · dsimp [History_on_turn, stolen_strat, pre_stolen_strat]
        rw [if_pos (by rfl), if_pos (by rfl)]
      · unfold stolen_strat
        rw [if_neg (by apply History_on_turn_nonempty_of_succ)]
        rw [show [ws ini [trap], trap] = [ws ini [trap]] ++ [trap] from (by simp only [List.singleton_append]) ]
        rw [← List.append_assoc]
        have := History_on_turn_stolen_getLast ini trap ws s_strat (t)
        have that := @List.dropLast_append_getLast _ (History_on_turn ini (stolen_strat trap ws) s_strat (t + 1)) (by apply History_on_turn_nonempty_of_succ)
        rw [← this]
        unfold stolen_strat at *
        rw [that]
        rw [ih]
        congr
        dsimp [History_on_turn]
        simp_rw [if_pos q]
    · simp_rw [if_neg q]
      rw [Turn_fst_not_step, not_not] at q
      rw [if_pos q]
      rw [List.cons_append, ih]
      dsimp [History_on_turn] at *
      rw [← @not_not (Turn_fst (t + 1 + 1)), ← Turn_fst_not_step] at q
      simp_rw [if_neg q] at *
      congr
      rw [← ih]
      rw [List.dropLast_append_cons]
      dsimp
      rw [List.append_nil]


lemma Chomp_len_heigh_legal (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) :
  Symm_Game_World.law (Chomp height length).toSymm_Game_World (Chomp height length).toSymm_Game_World.init_game_state [] (length, height) :=
  by
  dsimp [Chomp, preChomp]
  rw [if_pos ⟨Chomp_init_has_zero _ _ , (by trivial)⟩ ]
  rw [Chomp_state_empty]
  rw [if_pos (by intro con ; have := Chomp_init_has_len_hei height length ; rw [con, Finset.mem_singleton, Prod.eq_iff_fst_eq_snd_eq] at this ; cases' h with h h ; exact h this.2 ; exact h this.1 )]
  constructor
  · exact Chomp_init_has_len_hei height length
  · intro q qdef ; contradiction
  · apply List.Pairwise.nil
  · intro q qdef ; contradiction
  · intro con ; rw [Prod.eq_iff_fst_eq_snd_eq] at con ; cases' h with h h ; exact h con.2 ; exact h con.1


lemma Chomp_state_zero_top (height length : ℕ) (hist : List (ℕ × ℕ))
  (hh : hist ≠ []) (hm : ∀ q ∈ hist, q ∈ Chomp_init height length):
  Chomp_state (Chomp_init height length) hist = {(0, 0)} ↔ Chomp_state (Chomp_init height length) (hist ++ [(length, height)]) = {(0, 0)}  :=
  by
  cases' hist with x l
  · contradiction
  · have main : Chomp_state (Chomp_init height length) (x :: l) =  Chomp_state (Chomp_init height length) ((x :: l) ++ [(length, height)]) :=
      by
      dsimp [Chomp_state]
      apply Finset.filter_congr
      intro y _
      constructor
      · intro Q q qdef
        rw [← List.cons_append, List.mem_append] at qdef
        cases' qdef with qdef qdef
        · exact Q _ qdef
        · rw [List.mem_singleton] at qdef
          rw [qdef]
          specialize Q x (by exact List.mem_cons_self x l)
          specialize hm x (by exact List.mem_cons_self x l)
          simp_rw [Chomp_init, Finset.mem_product, Finset.mem_range, Nat.lt_succ] at hm
          dsimp [nondomi, domi] at *
          contrapose! Q
          exact ⟨le_trans hm.1 Q.1,  le_trans hm.2 Q.2⟩
      · intro Q q qdef
        rw [← List.cons_append] at Q
        apply Q
        exact List.mem_append_left [(length, height)] qdef
    rw [main]



lemma Chomp_state_zero_append_non_zero (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ)
  (hs : Chomp_state ini hist = {(0,0)}) (ha : act ≠ (0,0)) : Chomp_state ini (hist ++ [act]) = {(0,0)} :=
  by
  dsimp [Chomp_state] at *
  simp_rw [Finset.eq_singleton_iff_unique_mem, Finset.mem_filter] at *
  refine' ⟨⟨hs.1.1, _ ⟩, _ ⟩
  · intro q qdef
    rw [List.mem_append] at qdef
    cases' qdef with qdef qdef
    · exact hs.1.2 q qdef
    · rw [List.mem_singleton] at qdef
      rw [qdef]
      intro con
      dsimp [domi] at con
      simp_rw [Nat.le_zero] at con
      apply ha
      rw [Prod.eq_iff_fst_eq_snd_eq]
      exact con
  · intro x ⟨xi, xd⟩
    apply hs.2
    refine' ⟨ xi, _ ⟩
    intro q qdef
    apply xd
    exact List.mem_append.mpr (Or.inl qdef)


lemma Chomp_init_has_top (height length : ℕ) : (length, height) ∈ Chomp_init height length :=
  by
  simp_rw [Chomp_init, Finset.mem_product, Finset.mem_range, Nat.lt_succ]
  refine' ⟨ le_refl length , le_refl height ⟩




lemma fst_stolen_act_mem_init (height length : ℕ)
  (ws s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ)) (t : Nat) (tf : Turn_fst (Nat.succ t + 1))
  (leg : Chomp_law (Chomp_init height length)
      (History_on_turn (Chomp_init height length) (stolen_strat (length, height) ws) s_strat t)
      (s_strat (Chomp_init height length)
        (History_on_turn (Chomp_init height length) (stolen_strat (length, height) ws) s_strat t))) :
  ws (Chomp_init height length) [(length, height)] ∈ Chomp_init height length :=
  by
  cases' t with t
  · contradiction
  · have := History_on_turn_stolen_getLast (Chomp_init height length) (length, height) ws s_strat t
    rw [← this]
    apply leg.hist_mem
    apply List.getLast_mem


lemma pre_stolen_strat_legal_fst_helper_1 (height length : ℕ) (a b : Nat × Nat)
  (adef : a ∈ Chomp_init height length) (bdef : b ∈ Chomp_init height length)
  (main : nondomi b a) : nondomi (length, height) a :=
  by
  dsimp [nondomi, domi]
  dsimp [nondomi, domi] at main
  contrapose! main
  simp_rw [Chomp_init, Finset.mem_product, Finset.mem_range, Nat.lt_succ] at adef bdef
  convert bdef
  · exact le_antisymm adef.1 main.1
  · exact le_antisymm adef.2 main.2

lemma pre_stolen_strat_legal_fst_helper_2 (height length : ℕ) (act : Nat × Nat) (hist : List (Nat × Nat))
  (hh : hist ≠ [])
  (leg : Chomp_law (Chomp_init height length) hist act)
  (x : Nat × Nat) (xdef : x ∈ hist) : nondomi (length, height) x :=
  by
  have := leg.hist_nd
  rw [← List.dropLast_append_getLast hh, List.pairwise_append] at this
  rw [← List.dropLast_append_getLast hh, List.mem_append] at xdef
  cases' xdef with xdef xdef
  · replace this := this.2.2 _ xdef (List.getLast hist hh) (by exact List.mem_singleton.mpr rfl)
    apply pre_stolen_strat_legal_fst_helper_1 _ _ _ _ _ _ this
    · apply leg.hist_mem
      exact List.mem_of_mem_dropLast xdef
    · apply leg.hist_mem
      exact List.getLast_mem hh
  · rw [List.mem_singleton] at xdef
    rw [xdef]









--#exit

lemma pre_stolen_strat_legal_fst (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0)
  (ws s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law (stolen_strat (length, height) ws) s_strat)
  : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law (pre_stolen_strat (length, height)  s_strat) ws :=
  by
  intro t tf
  cases' t with t
  · dsimp!
    unfold pre_stolen_strat
    rw [if_pos (by rfl)]
    apply Chomp_len_heigh_legal _ _ h
  · rw [← History_on_turn_stolen_pre_stolen]
    simp only [ne_eq, pre_stolen_strat, List.append_eq_nil, and_false, List.dropLast_concat, ite_false]
    have f_leg' := f_leg t (by rw [Turn_snd_fst_step] ; exact tf)
    dsimp [Chomp, preChomp]
    dsimp [Chomp, preChomp] at f_leg'
    have : History_on_turn (Chomp_init height length) (stolen_strat (length, height) ws) s_strat t ≠ [] :=
        by
        cases' t with t
        · contradiction
        · apply History_on_turn_nonempty_of_succ
    by_cases qwlog : (0, 0) ∈ History_on_turn (Chomp_init height length) (stolen_strat (length, height) ws) s_strat t
    · rw [if_neg (by rw [not_and_or,not_not] ; right ; apply List.mem_append_left ; exact qwlog )]
      exact trivial
    · rw [if_pos ⟨Chomp_init_has_zero _ _, qwlog⟩] at f_leg'
      rw [if_pos ⟨Chomp_init_has_zero _ _, (by apply List.not_mem_append qwlog (helper _ _ h))⟩]
      by_cases q : ¬Chomp_state (Chomp_init height length) (History_on_turn (Chomp_init height length) (stolen_strat (length, height) ws) s_strat t) = {(0, 0)}
      · rw [if_pos q] at f_leg'
        replace this := Chomp_state_zero_top height length _ this f_leg'.hist_mem
        rw [← not_iff_not] at this
        rw [this] at q
        rw [if_pos q]
        constructor
        · exact f_leg'.act_mem
        · intro q qdef
          rw [List.mem_append] at qdef
          cases' qdef with qdef qdef
          · exact f_leg'.hist_mem q qdef
          · rw [List.mem_singleton] at qdef
            rw [qdef]
            apply Chomp_init_has_top
        · rw [List.pairwise_append]
          refine' ⟨(by apply f_leg'.hist_nd), (by apply List.pairwise_singleton), _ ⟩
          intro a adef b bdef
          rw [List.mem_singleton] at bdef
          rw [bdef]
          sorry
        · intro a adef
          rw [List.mem_append] at adef
          cases' adef with adef adef
          · exact f_leg'.nd _ adef
          · rw [List.mem_singleton] at adef
            rw [adef]
            have : nondomi (ws (Chomp_init height length) [(length, height)]) (s_strat (Chomp_init height length) (History_on_turn (Chomp_init height length) (stolen_strat (length, height) ws) s_strat t)) :=
              by
              apply f_leg'.nd
              cases' t with t
              · contradiction
              · rw [← History_on_turn_stolen_getLast (Chomp_init height length) (length, height) ws s_strat t]
                apply List.getLast_mem
            apply pre_stolen_strat_legal_fst_helper_1 _ _ _ _ (f_leg'.act_mem) (fst_stolen_act_mem_init _ _ _ _ _ tf f_leg') this
        · exact f_leg'.nz_act
      · rw [if_neg q] at f_leg'
        rw [not_not] at q
        replace q := Chomp_state_zero_append_non_zero _ _ (length, height) q (by intro con ; rw [Prod.eq_iff_fst_eq_snd_eq] at con ; cases' h with h h ; apply h ; exact con.2 ; apply h ; exact con.1)
        rw [if_neg (by rw [not_not]; apply q)]
        exact f_leg'



-- trouble on whether act isn't (len, height) → hist non empty, and act legal should imply it...


lemma Strong_strategy_stealing (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) : (Chomp height length).is_fst_win :=
  by
  cases' (zSymm_Game_World.Zermelo (Chomp height length) (Chomp_WLT _ _ h)) with F S
  · exact F
  · obtain ⟨ws, ws_prop⟩ := S
    use (stolen_strat (length, height) ws)
    intro s_strat s_leg

-- TODO : replace wining strat def so that request ∀ t, leg f at t → leg ws at (t+1) ...


-- initial stealing stuff
#exit
lemma Chomp_Stealing_condition (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) : Strong_stealing_condition (Chomp height length) :=
  by
  use (length, height)
  constructor
  · dsimp [Chomp, preChomp]
    rw [if_pos ⟨Chomp_init_has_zero _ _ , (by trivial)⟩ ]
    rw [Chomp_state_empty]
    rw [if_pos (by intro con ; have := Chomp_init_has_len_hei height length ; rw [con, Finset.mem_singleton, Prod.eq_iff_fst_eq_snd_eq] at this ; cases' h with h h ; exact h this.2 ; exact h this.1 )]
    constructor
    · exact Chomp_init_has_len_hei height length
    · intro q qdef ; contradiction
    · apply List.Pairwise.nil
    · intro q qdef ; contradiction
    · intro con ; rw [Prod.eq_iff_fst_eq_snd_eq] at con ; cases' h with h h ; exact h con.2 ; exact h con.1
  · intro act hist leg hne htop
    constructor
    · apply preChomp_law_prop_transition _ _ h _ _ leg
    · apply preChomp_law_prop_law _ _ h _ _ hne htop leg


--#exit

lemma pre_stolen_strat_legal_fst (height length : ℕ) (h : height ≠ 0 ∨ length ≠ 0) --(hgu : g.strat_unique_actions)
  (ws s_strat : Strategy (Finset (ℕ × ℕ)) (ℕ × ℕ))
  (f_leg : Strategy_legal_snd (Chomp height length).init_game_state (Chomp height length).law (stolen_strat (Chomp height length) (Chomp_Stealing_condition _ _ h) ws) s_strat)
  : Strategy_legal_fst (Chomp height length).init_game_state (Chomp height length).law (pre_stolen_strat (Chomp height length) (Chomp_Stealing_condition _ _ h) s_strat) ws :=
  by
  intro t tf
  cases' t with t
  · dsimp!
    unfold pre_stolen_strat
    rw [if_pos (by rfl)]
    apply (Classical.choose_spec (Chomp_Stealing_condition _ _ h)).1
  · rw [← History_on_turn_stolen_pre_stolen]
    simp only [ne_eq, pre_stolen_strat, List.append_eq_nil, and_false, List.dropLast_concat, ite_false]
    have f_leg' := f_leg t (by rw [Turn_snd_fst_step] ; exact tf)
    dsimp [Chomp, preChomp]
    dsimp [Chomp, preChomp] at f_leg'

  -- induction' t with t ih
  -- · dsimp!
  --   unfold pre_stolen_strat
  --   rw [if_pos (by rfl)]
  --   apply (Classical.choose_spec (Chomp_Stealing_condition _ _ h)).1
  -- · rw [← History_on_turn_stolen_pre_stolen]
  --   simp only [ne_eq, pre_stolen_strat, List.append_eq_nil, and_false, List.dropLast_concat, ite_false]
  --   have f_leg' := f_leg t (by rw [Turn_snd_fst_step] ; exact tf)
  --   cases' t with t
  --   · contradiction
  --   · sorry
