/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Positional





structure pairProp {win_sets : Finset (Finset α)} (win_set : win_sets) (p : α × α) : Prop where
  dif : p.1 ≠ p.2
  mem_fst : p.1 ∈ win_set.val
  mem_snd : p.2 ∈ win_set.val



def pre_Pairing_condition [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) : Prop :=
   ∀ w : win_sets, ∃ p : α × α, pairProp w p


noncomputable
def pairing [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (h : pre_Pairing_condition win_sets) :=
  @Classical.choose (win_sets → (α × α)) (fun f : win_sets → (α × α) => ∀ (x : { x // x ∈ win_sets }), pairProp x (f x)) (@Classical.axiomOfChoice _ _ pairProp h)


lemma pairing_prop [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (h : pre_Pairing_condition win_sets) :
  ∀ (x : { x // x ∈ win_sets }), pairProp x ((pairing h) x)  :=
  @Classical.choose_spec (win_sets → (α × α)) (fun f : win_sets → (α × α) => ∀ (x : { x // x ∈ win_sets }), pairProp x (f x)) (@Classical.axiomOfChoice _ _ pairProp h)

structure pairDif (a b : α × α) : Prop where
  strait_fst : a.1 ≠ b.1
  strait_snd : a.1 ≠ b.1
  cross_fst : a.1 ≠ b.2
  cross_snd : a.2 ≠ b.1


structure Pairing_condition [DecidableEq α] [Fintype α] (win_sets : Finset (Finset α)) where
  has_pairing : pre_Pairing_condition win_sets
  pairing_dif : ∀ w v : win_sets, w ≠ v → pairDif ((pairing has_pairing) w) ((pairing has_pairing) v)



noncomputable
def Pairing_StratCore [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (hg : Pairing_condition win_sets) :
  (hist : List α) → (leg : Hist_legal (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_legal (Positional_Game_World win_sets).snd_legal hist) → α :=
  fun hist leg =>
    let spam :=
      if T : Turn_fst (hist.length + 1)
            then
              Classical.choose (((Positional_Game_World_playable win_sets) hist (leg)).1 T)
            else
              Classical.choose (((Positional_Game_World_playable win_sets) hist (leg)).2 (by rw [Turn_snd_iff_not_fst] ; exact T))
    match hist with
    | last :: _ =>
        if hxf : ∃ w : win_sets, last = (pairing hg.has_pairing w).1
        then
          let other := (pairing hg.has_pairing (Classical.choose hxf)).2
          if other ∈ hist
          then spam
          else other
        else
          if hxs : ∃ w : win_sets, last = (pairing hg.has_pairing w).2
          then
            let other := (pairing hg.has_pairing (Classical.choose hxs)).1
            if other ∈ hist
            then spam
            else other
          else
            spam
    | [] => spam




noncomputable
def Pairing_fStrat [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)}  (hg : Pairing_condition win_sets) :
  fStrategy (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_legal (Positional_Game_World win_sets).snd_legal :=
  fun hist T leg =>
    ⟨ Pairing_StratCore hg hist leg,
      (by
       dsimp [Positional_Game_World]
       split_ifs with N
       cases' hist with last L
       · dsimp [Pairing_StratCore]
         rw [dif_pos (by decide)]
         exact
           List.not_mem_nil
             (Classical.choose
               (Pairing_StratCore.proof_1 [] leg (of_decide_eq_true (Eq.refl true))))
       · dsimp [Pairing_StratCore]
         by_cases hxf : ∃ w : win_sets, last = (pairing hg.has_pairing w).1
         · rw [dif_pos hxf]
           split_ifs with M
           · have := Classical.choose_spec (Pairing_StratCore.proof_1 (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · have := Classical.choose_spec (Pairing_StratCore.proof_1 (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · exact M
         · rw [dif_neg hxf]
           by_cases hxs : ∃ w : win_sets, last = (pairing hg.has_pairing w).2
           · rw [dif_pos hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · exact M
           · rw [dif_neg hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_1 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
       )
      ⟩


noncomputable
def Pairing_sStrat [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)}  (hg : Pairing_condition win_sets) :
  sStrategy (Positional_Game_World win_sets).init_game_state (Positional_Game_World win_sets).fst_legal (Positional_Game_World win_sets).snd_legal :=
  fun hist T leg =>
    ⟨ Pairing_StratCore hg hist leg,
      (by
       dsimp [Positional_Game_World]
       split_ifs with N
       cases' hist with last L
       · dsimp [Pairing_StratCore]
         rw [dif_pos (by decide)]
         exact
           List.not_mem_nil
             (Classical.choose
               (Pairing_StratCore.proof_1 [] leg (of_decide_eq_true (Eq.refl true))))
       · dsimp [Pairing_StratCore]
         by_cases hxf : ∃ w : win_sets, last = (pairing hg.has_pairing w).1
         · rw [dif_pos hxf]
           split_ifs with M
           · have := Classical.choose_spec (Pairing_StratCore.proof_2 (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · have := Classical.choose_spec (Pairing_StratCore.proof_2 (last :: L) leg (T))
             dsimp [Positional_Game_World] at this
             rw [if_pos N] at this
             exact this
           · exact M
         · rw [dif_neg hxf]
           by_cases hxs : ∃ w : win_sets, last = (pairing hg.has_pairing w).2
           · rw [dif_pos hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · exact M
           · rw [dif_neg hxs]
             split_ifs with M
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
             · have := Classical.choose_spec (Pairing_StratCore.proof_2 (last :: L) leg (T))
               dsimp [Positional_Game_World] at this
               rw [if_pos N] at this
               exact this
       )
      ⟩


/-
- Show that the size preimage under `State_from_history` of α of 0 (aka non claimed tiles) decreases at each turn that is neutral (should be true in any positional game)
- show that the set of turns that are neutral is upperbounded by Fintype.card α
- Argue with finitenenss of decreasing sequence of nats (Fintype.card α - t), cause API for maximum doesn't seem to exist ; maybe write that API
  Alternatively, argue over infiteness ? derive not infinite via upperbound  and the use finset amximum API ?
- disjoin on turn after last neutral turn : if its a draw or snd_win, we've got the theorem
- show that it can't be a first win as follows:
  - if it were, there'd be a monochromatic win set
  - for that win set, consider the first turn such that one of the paring elems was colored
  - it should be colored by fst, since the win set is monchrome for fst
  - the other pair elem shouldn't be colored, by minimality
  - on the next turn, snd - playning the airing strat, will color the other pair
  - this contradictics the assumption that all points of the win set are colored by fst

This is gonna ake ages
-/



theorem Pairing_Strategy [Inhabited α] [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)}  (hg : Pairing_condition win_sets) :
  (Positional_Game_World win_sets).is_draw_at_worst_snd :=
  by
  use Pairing_sStrat hg
  intro f_strat
  sorry

#check Game_wDraw.draw



#exit

-- # Alternative

structure pairDif (a b : α × α) : Prop where
  strait_fst : a.1 ≠ b.1
  strait_snd : a.1 ≠ b.1
  cross_fst : a.1 ≠ b.2
  cross_snd : a.2 ≠ b.1

structure Pairing_condition [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (g : Positional_Game_World win_sets) where
  playable : g.playable
  pairing : List (α × α)
  pairing_dif_inner : ∀ p ∈ pairing, p.1 ≠ p.2
  pairing_dif_outer : List.Pairwise pairDif pairing
  pairing_mem : ∀ w ∈ win_sets, ∃ n : Fin pairing.length, (pairing.get n).1 ∈ w ∧ (pairing.get n).2 ∈ w
  -- should make the paring strat computable, if the element chosen in by playability are ... (via List.find?)
  -- probably makes proofs of pairing_mem much more difficult ; I believe Hall is non-constructive in mathlib, so whats the point anyway




-- Initial stuff
#exit

structure Game_World.pairing_prop_pairdiff_fst
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (w' v : (γ → Fin 3))
  (hw' : fst_win_states g w')
  (hv : fst_win_states g v)
  : Prop where
  d2 : (p w' hw).1 ≠ (p v hv).1
  d3 : (p w' hw).2 ≠ (p v hv).2
  d4 : (p w' hw).1 ≠ (p v hv).2
  d5 : (p w' hw).2 ≠ (p v hv).1

structure Game_World.pairing_prop_fst
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (w' : (γ → Fin 3))
  (hw' : fst_win_states g w')
  : Prop where
  d : (p w' hw').1 ≠ (p w' hw').2
  ff : (w' (p w' hw').1 = 1)
  sf : (w' (p w' hw').2 = 1)


def Game_World.pairing_fst
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))  : Prop :=
    (∀ (w' : (γ → Fin 3)), (hw' : g.fst_win_states w') →
      ( g.pairing_prop_fst p w' hw' ∧
        (∀ (v : (γ → Fin 3)), (hv : g.fst_win_states v) → v ≠ w' →
          g.pairing_prop_pairdiff_fst p w' v hw' hv)))


def Game_World.has_pairing_fst
  (g : Game_World (γ → Fin 3) γ) : Prop :=
  ∃ p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ),
    g.pairing_fst p

def Game_World.pairing_pairs
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ)) :
  Set γ :=
  {pts : γ | ∃ s : (γ → Fin 3), ∃ hw : g.fst_win_states s,  pts = (p s hw).1 ∨ pts = (p s hw).2}


open Classical

noncomputable
def Game_World.snd_pairing_strat
  [Inhabited γ]
  (g : Game_World (γ → Fin 3) γ)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  : Strategy (γ → Fin 3) γ :=
  fun ini hist =>
    match hist with
    | [] => default
    | prev :: h => if h_mem : prev ∈ g.pairing_pairs p
                   then (show γ from (
                      by
                      dsimp [Game_World.pairing_pairs] at h_mem
                      choose s hw prop using h_mem
                      -- cases' prop with
                      -- · sorry -- expected checkColGt
                      -- · sorry
                      by_cases q :  prev = (p s hw).1 -- if prev is fst of pair
                      · by_cases k : ∃ a : γ, a ∉ (prev :: h) -- if there are tiles left
                        · by_cases K : (p s hw).2 ∉ (prev :: h) -- if the second of pair isn't taken
                          · exact (p s hw).2 --then select second of pair
                          · choose a _ using k -- else chose some available tile
                            exact a
                        · exact default -- should never occur
                      · rw [or_iff_right q] at prop
                        exact (p s hw).1 -- else choose first tile

                   ))
                   else (show γ from (
                          by
                          by_cases k : ∃ a : γ, a ∉ (prev :: h)
                          · choose a _ using k
                            exact a
                          · exact default
                   ))

#print Game_World.snd_pairing_strat

theorem Game.has_pairing_invariant_part1
  [Inhabited γ]
  (g : Game (γ → Fin 3) γ)
  (hp : g.has_pairing_fst)
  {T : ℕ} (ht : g.must_terminate_before T)
  (hlf : g.fst_legal = fun hist act => act ∉ hist) -- add pos game transition too ?
  (hls : g.snd_legal = fun hist act => act ∉ hist)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (hp : g.pairing_fst p)
  (hss : g.snd_strat = g.snd_pairing_strat p)
  (special : ¬ (g.fst_win_states g.init_game_state))
  :
  ∀ turn : ℕ, (w : g.fst_win_states (g.state_on_turn turn)) →
  (g.state_on_turn turn) (p (g.state_on_turn turn) w).1 = 1 →
  (g.state_on_turn (turn + 1)) (p (g.state_on_turn (turn)) w).2 = 2 :=
  by
  intro t
  induction' t with t ih
  · dsimp [state_on_turn, history_on_turn, History_on_turn]
    rw [if_pos (by decide)]
    intro w fst_tile
    exfalso
    exact special w
  · sorry



#exit

theorem Game.has_pairing_invariant
  [Inhabited γ]
  (g : Game (γ → Fin 3) γ)
  (hp : g.has_pairing_fst)
  {T : ℕ} (ht : g.must_terminate_before T)
  (hlf : g.fst_legal = fun hist act => act ∉ hist) -- add pos game transition too ?
  (hls : g.snd_legal = fun hist act => act ∉ hist)
  (p : (s : (γ → Fin 3)) → (hw : g.fst_win_states s) → (γ × γ))
  (hp : g.pairing_fst p)
  (hss : g.snd_strat = g.snd_pairing_strat p)
  (nontrivial : ¬ g.fst_win_states (g.fst_transition [] (g.fst_strat g.init_game_state []) )):
  ∀ turn : ℕ, g.snd_win_states (g.state_on_turn turn) ∨ g.state_on_turn_neutral turn :=
  by
  intro t
  apply @Nat.induct_2_step (fun t => Game_World.snd_win_states g.toGame_World (state_on_turn g t) ∨ state_on_turn_neutral g t)
  · dsimp [state_on_turn, state_on_turn_neutral]
    rw [if_neg (by decide)]
    apply Classical.em
  · dsimp [state_on_turn, state_on_turn_neutral]
    rw [if_pos (by decide), if_pos (by decide), history_on_turn, History_on_turn]
    right
    exact nontrivial
  · intro n c1 c2
    rw [or_iff_not_imp_left]
    intro c3
    dsimp [state_on_turn_neutral]
    split_ifs with tn
    · intro con
      specialize hp (state_on_turn g (n + 2)) con
      obtain ⟨⟨h_d, h_ff, h_sf ⟩, h_diff⟩ := hp
      -- unfold snd_strat to pairing strat to derive contra...
    · exact c3

#check Nat.induct_2_step

#exit


theorem Game_World.has_pairing_is_snd_draw
  (g : Game_World (γ → Fin 3) γ)
  (hp : g.has_pairing_fst)
  {T : ℕ} (ht : g.must_terminate_before T)
  (hlf : g.fst_legal = fun hist act => act ∉ hist) -- add pos game transition too ?
  (hls : g.snd_legal = fun hist act => act ∉ hist) :
  g.is_snd_win ∨ g.is_snd_draw :=
  by
  sorry



#exit

-- Positional version:

structure pairing_prop_aux
  (win_sets : Finset (Finset α))
  (p : (w : Finset α) → (hw : w ∈ win_sets) → (α × α))
  (w' v : Finset α)
  (hw : w' ∈ win_sets)
  (hv : v ∈ win_sets)
  : Prop where
  d2 : (p w' hw).1 ≠ (p v hv).1
  d3 : (p w' hw).2 ≠ (p v hv).2
  d4 : (p w' hw).1 ≠ (p v hv).2
  d5 : (p w' hw).2 ≠ (p v hv).1


def Positional_Game_World.has_pairing (win_sets : Finset (Finset α)) :=
  ∃ p : (w : Finset α) → (hw : w ∈ win_sets) → (α × α),
    ∀ w' : Finset α, (hw : w' ∈ win_sets) →
      ((p w' hw).1 ≠ (p w' hw).2) ∧
      (∀ v : Finset α, (hv : v ∈ win_sets) → v ≠ w' →
          pairing_prop_aux win_sets p w' v hw hv)
