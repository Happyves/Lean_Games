/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Stealing

#exit
/-
This file describes the game of Chomp and proves that the first player has a winning strategy for it.
The game of chomp is played on a `hight` × `length` grid-like board. At each turn, a player may select
a tile of the board. From there on, all tiles dominated (wrt. lexicographic order) by that tile may not
be selected anymore (think of the board as of a chocolate bar, who's tiles are getting "chomped" off).
The player that eats the last tile loses the game.

The main concept are:
- `preChomp` defines the game of chomp, `Chomp` glues the Zermelo properties to it
- `Chomp_stealing_condition` shows that Chomp satisfies the stealing conditions
- `Chomp_is_fst_win` show that Chomp has a winning strategy for the first player, via strategy stealing.

-/


-- # Chomp state lemmata

/-- a grid-point is dominated by another if both its coordinates are smaller-/
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


/-- The current board is obtained by considering all tiles from the
initial board, that aren't dominated by a tile played sofar
-/
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


/-- The initial board is a rectangle-/
def Chomp_init (height length : ℕ) := (Finset.range (length+1)) ×ˢ (Finset.range (height+1))



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




lemma Chomp_init_has_zero (height length : ℕ)  : (0,0) ∈ Chomp_init height length :=
  by
  dsimp [Chomp_init]
  simp_rw [Finset.mem_product, Finset.mem_range, and_comm]
  constructor <;> {exact Nat.add_pos_right _ Nat.le.refl}


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


/--
Selecting a tile `act` is legal, if it was in the initial board,
and it isn't dominated by one of the tiles played sofar.
-/
structure Chomp_law (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) (act : ℕ × ℕ) : Prop where
  act_mem : act ∈ ini
  nd : ∀ q ∈ hist, nondomi q act





-- # Chomp win states lemmata

/--
A terminal position is reached when playing `final_a` at history `final_h`,
if the board wasn't empty at that history, but is after playing the move.
To have a coherent end for this game, all histories extending such a history
are also considered terminal.
-/
structure Chomp_win_final (ini : Finset (ℕ × ℕ)) (hist final_h : List (ℕ × ℕ)) (final_a : ℕ × ℕ) : Prop where
  N : Chomp_state ini final_h ≠ ∅
  F : Chomp_state ini (final_a :: final_h) = ∅
  ref : (final_a :: final_h) <:+ hist

/--
The game is won by the frist player if the terminal position was reached on the second turn.
-/
def Chomp_win_fst (ini : Finset (ℕ × ℕ)) (hist : List (ℕ × ℕ)) : Prop :=
  ∃ final_h : List (ℕ × ℕ), ∃ final_a : (ℕ × ℕ), Turn_snd (final_h.length + 1) ∧ Chomp_win_final ini hist final_h final_a

/--
The game is won by the second player if the terminal position was reached on the first turn.
-/
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
  fst_win_states := fun hist => Chomp_win_fst (Chomp_init height length) hist
  snd_win_states := fun hist => Chomp_win_snd (Chomp_init height length) hist
  transition := fun hist act => Chomp_state (Chomp_init height length) (act :: hist)
  law := fun hist act =>  if Chomp_state (Chomp_init height length) hist ≠ ∅
                          then Chomp_law (Chomp_init height length) hist act
                          else True



-- # Chomp is WL


lemma preChomp_state_sub {height length : ℕ}
  (f_strat : (preChomp height length).fStrategy) (s_strat : (preChomp height length).sStrategy) :
  ∀  n,  Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n+1))
    ⊆ Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n)) :=
    by
    intro n
    dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
    split_ifs with T
    · dsimp
      apply Chomp_state_sub_cons
    · dsimp
      apply Chomp_state_sub_cons



lemma preChomp_state_ssub {height length : ℕ}
  (f_strat : (preChomp height length).fStrategy)
  (s_strat : (preChomp height length).sStrategy) :
  ∀  n,  Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n)) ≠ ∅ →
    Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n+1))
    ⊂ Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n)) :=
    by
    intro n hn
    rw [Finset.ssubset_iff_of_subset (preChomp_state_sub f_strat s_strat n)]
    dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
    split_ifs with T
    · dsimp
      let act := (f_strat ((preChomp height length).hist_on_turn f_strat s_strat (n)).val (by rw [Symm_Game_World.hist_on_turn_length] ; exact T) ((preChomp height length).hist_on_turn f_strat s_strat (n)).prop.1)
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
      let act := (s_strat ((preChomp height length).hist_on_turn f_strat s_strat (n)).val (by rw [Symm_Game_World.hist_on_turn_length] ; exact T) ((preChomp height length).hist_on_turn f_strat s_strat (n)).prop.1)
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
  (f_strat : (preChomp height length).fStrategy)
  (s_strat : (preChomp height length).sStrategy) :
  ∃ n, Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n+1)) = ∅ ∧
    ∀ m ≤ n, Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (m)) ≠ ∅ :=
  by
  let states := {s | ∃ n, s = Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n)) ∧ s ≠ ∅}
  have lem : Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat 0).val ≠ ∅ :=
    by
    dsimp only [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn, Chomp_state, preChomp]
    rw [Finset.filter_true_of_mem]
    · rw [← Finset.nonempty_iff_ne_empty]
      use (length, height)
      apply Chomp_init_has_len_hei height length
    · intro _ _ _ no
      contradiction
  have states_nonempty : Set.Nonempty states := by
    use  Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat 0)
    use 0
  obtain ⟨n,ndef,ne⟩ := WellFounded.min_mem Finset.isWellFounded_ssubset.wf states states_nonempty
  use n
  constructor
  · by_contra con
    apply @WellFounded.not_lt_min _ _ Finset.isWellFounded_ssubset.wf states states_nonempty (Chomp_state (preChomp height length).init_game_state ((preChomp height length).hist_on_turn f_strat s_strat (n+1))) (by use n+1)
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
    apply Symm_Game_World.hist_on_turn_suffix
    exact mln



lemma preChomp_isWL (height length : ℕ) : (preChomp height length).isWL :=
  by
  intro f_strat s_strat
  obtain ⟨T,Tdef⟩ := preChomp_reaches_empty f_strat s_strat
  use (T+1)
  by_cases Tt : Turn_fst (T+1)
  · apply Game_World.Turn_isWL.ws
    dsimp [preChomp, Chomp_win_snd]
    use ((preChomp height length).hist_on_turn f_strat s_strat T)
    use f_strat ((preChomp height length).hist_on_turn f_strat s_strat T).val (by rw [Symm_Game_World.hist_on_turn_length] ; exact Tt) ((preChomp height length).hist_on_turn f_strat s_strat T).prop.1
    constructor
    · rw [Symm_Game_World.hist_on_turn_length] ; exact Tt
    · constructor
      · apply Tdef.2
        apply le_refl
      · convert Tdef.1
        dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
        rw [dif_pos Tt]
      · dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
        rw [dif_pos Tt]
        apply List.suffix_refl
  · apply Game_World.Turn_isWL.wf
    dsimp [preChomp, Chomp_win_snd]
    use ((preChomp height length).hist_on_turn f_strat s_strat T)
    use s_strat ((preChomp height length).hist_on_turn f_strat s_strat T).val (by rw [Symm_Game_World.hist_on_turn_length] ; exact Tt) ((preChomp height length).hist_on_turn f_strat s_strat T).prop.1
    constructor
    · rw [Symm_Game_World.hist_on_turn_length] ; exact Tt
    · constructor
      · apply Tdef.2
        apply le_refl
      · convert Tdef.1
        dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
        rw [dif_neg Tt]
      · dsimp [Symm_Game_World.hist_on_turn, Game_World.hist_on_turn]
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

lemma Bait_leg_fst (height length : ℕ) : (Chomp height length).law [] (length, height) :=
  by
  dsimp [Chomp, preChomp]
  rw [if_pos (by apply Chomp_state_empty_not_empty)]
  constructor
  · apply Chomp_init_has_len_hei
  · intro _ no
    contradiction

lemma Bait_leg_imp {height length : ℕ} (h : height ≠ 0 ∨ length ≠ 0) :
  ∀ hist, ∀ act, (Chomp height length).hist_legal (hist) →
    (Chomp height length).law (hist ++ [(length, height)]) act → (Chomp height length).law (hist) act :=
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

lemma Bait_leg_imp' {height length : ℕ} (h : height ≠ 0 ∨ length ≠ 0) :
  ∀ hist, ∀ act, (Chomp height length).hist_legal (hist) →
    (Z : ¬ hist = []) → hist.getLast Z = (length, height) → Turn_fst (hist.length + 1) → (Chomp height length).law hist.dropLast act → (Chomp height length).law hist act :=
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
            dsimp at now
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


lemma Chomp_Bait {height length : ℕ} (h : height ≠ 0 ∨ length ≠ 0) : Bait (Chomp height length) (length, height) :=
  {leg_fst := Bait_leg_fst height length, leg_imp := Bait_leg_imp h, leg_imp' := Bait_leg_imp' h}


lemma Chomp_not_init_win {height length : ℕ} : ¬ (Chomp height length).snd_win_states [] :=
  by
  dsimp [Chomp, preChomp, Chomp_win_snd]
  push_neg
  intro h a _ con
  replace con := con.ref
  rw [List.suffix_nil] at con
  contradiction





lemma List.ne_empty_of_mem {l : List α} {x : α} (h : x ∈ l) : l ≠ [] := by
  cases' l with _ _
  · contradiction
  · apply List.noConfusion


lemma List.singleton_suffix  {l : List α} {x : α} (h : [x] <:+ l) : x = l.getLast (List.ne_empty_of_mem (List.mem_of_suffix h (List.mem_cons_self x []))) := by
  obtain ⟨t,td⟩ := h ; simp_rw [← td, List.getLast_append]


lemma Chomp_winning_equiv {height length : ℕ} (H : height ≠ 0 ∨ length ≠ 0) :
  ∀ hist, (Chomp height length).hist_legal hist → (Chomp height length).snd_win_states (hist ++ [(length, height)]) → (Chomp height length).fst_win_states hist :=
  by
  intro h _
  intro q
  dsimp [Chomp, preChomp, Chomp_win_fst, Chomp_win_snd] at *
  obtain ⟨hist,act,T,W⟩ := q
  use (hist.dropLast)
  use act
  have fact : hist ≠ [] :=
    by
    intro con
    rw [con] at W
    have oh := W.ref
    have no := W.F
    replace oh := List.singleton_suffix oh
    rw [List.getLast_append] at oh
    rw [oh] at no
    replace no := Chomp_state_state_empty _ (Chomp_init_has_zero height length) _ no
    apply helper _ _ H no
  have : hist = hist.dropLast ++ [(length,height)] :=
    by
    nth_rewrite 1 [← List.dropLast_append_getLast fact]
    congr
    obtain ⟨t,tdef⟩ := W.ref
    have : List.getLast (t ++ act :: hist) (by apply List.append_ne_nil_of_ne_nil_right ; apply List.noConfusion) = List.getLast (h ++ [(length, height)]) (by apply List.append_ne_nil_of_ne_nil_right ; apply List.noConfusion) := by simp_rw [tdef]
    simp_rw [List.getLast_append] at this
    simp_rw [List.getLast_append' t (act :: hist) List.noConfusion] at this
    simp_rw [List.getLast_cons fact] at this
    exact this
  constructor
  · rw [List.length_dropLast, Nat.sub_add_cancel (by rw [Nat.succ_le, List.length_pos] ; apply fact), Turn_snd_fst_step] ; exact T
  · constructor
    · intro con
      apply W.N
      rw [← Finset.subset_empty] at *
      rw [← List.dropLast_append_getLast fact]
      apply Finset.Subset.trans _ con
      apply Chomp_state_sub
    · apply Chomp_state_hist_zero
      have that := Chomp_state_state_empty _ (Chomp_init_has_zero height length) _ W.F
      rw [this, ← List.cons_append, List.mem_append] at that
      cases' that with q q
      · exact q
      · exfalso
        apply helper _ _ H q
    · replace W := W.ref
      rw [this, ← List.cons_append] at W
      obtain ⟨t,td⟩ := W
      rw [← List.append_assoc] at td
      replace td := List.append_inj_left' td rfl
      use t

/--
Chomp satisfies the stealing conditions.

Suppose the second player has a winning strategy. The frist player may steal it as follows.
The frist player considers playing the top-most outer-most tile of the board, and considers the response of the second player.
The frist player can play that response from the start, pretending to be the second player, acting as if the actual player
was the first player and had played the top-most outer-most tile as a first move.
-/
lemma Chomp_stealing_condition {height length : ℕ} (H : height ≠ 0 ∨ length ≠ 0) : Stealing_condition (Chomp height length) where
  trap := (length, height)
  hb := Chomp_Bait H
  fst_not_win := Chomp_not_init_win
  wb := Chomp_winning_equiv H


theorem Chomp_is_fst_win {height length : ℕ} (H : height ≠ 0 ∨ length ≠ 0) :
  (Chomp height length).is_fst_win  :=
  by
  apply Strategy_stealing
  apply Chomp_stealing_condition H
