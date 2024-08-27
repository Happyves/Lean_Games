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



structure pre_Pairing_condition [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (g : Positional_Game_World win_sets) : Prop where
  playable : g.playable
  pairing : ∀ w : win_sets, ∃ p : α × α, pairProp w p -- keep pairing in prop form for covience as its probaly easier to prove
  --pairing! := @Classical.choose (win_sets → (α × α)) (fun f : win_sets → (α × α) => ∀ (x : { x // x ∈ win_sets }), pairProp x (f x)) (@Classical.axiomOfChoice _ _ pairProp pairing)
  -- ↑ adding noncomputable raises errors though ; might be fixed when updating ?!?


noncomputable
def pairing! [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {g : Positional_Game_World win_sets} (h : pre_Pairing_condition g) :=
  @Classical.choose (win_sets → (α × α)) (fun f : win_sets → (α × α) => ∀ (x : { x // x ∈ win_sets }), pairProp x (f x)) (@Classical.axiomOfChoice _ _ pairProp h.pairing)


lemma pairing!_prop [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {g : Positional_Game_World win_sets} (h : pre_Pairing_condition g) :
  ∀ (x : { x // x ∈ win_sets }), pairProp x ((pairing! h) x)  :=
  @Classical.choose_spec (win_sets → (α × α)) (fun f : win_sets → (α × α) => ∀ (x : { x // x ∈ win_sets }), pairProp x (f x)) (@Classical.axiomOfChoice _ _ pairProp h.pairing)

structure pairDif (a b : α × α) : Prop where
  strait_fst : a.1 ≠ b.1
  strait_snd : a.1 ≠ b.1
  cross_fst : a.1 ≠ b.2
  cross_snd : a.2 ≠ b.1


structure Pairing_condition [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} (g : Positional_Game_World win_sets) extends pre_Pairing_condition g where
  pairing_dif : ∀ w v : win_sets, w ≠ v → pairDif ((pairing! topre_Pairing_condition) w) ((pairing! topre_Pairing_condition) v)



noncomputable
def Pairing_StratCore [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {g : Positional_Game_World win_sets} (hg : Pairing_condition g) :
  (hist : List α) → (leg : Hist_legal g.init_game_state g.fst_legal g.snd_legal hist) → α :=
  fun hist leg =>
    let spam :=
      if T : Turn_fst (hist.length + 1)
            then
              Classical.choose ((hg.playable hist (leg)).1 T)
            else
              Classical.choose ((hg.playable hist (leg)).2 (by rw [Turn_snd_iff_not_fst] ; exact T))
    match hist with
    | last :: _ =>
        if hxf : ∃ w : win_sets, last = (pairing! hg.topre_Pairing_condition w).1
        then
          let other := (pairing! hg.topre_Pairing_condition (Classical.choose hxf)).2
          if other ∈ hist
          then spam
          else other
        else
          if hxs : ∃ w : win_sets, last = (pairing! hg.topre_Pairing_condition w).2
          then
            let other := (pairing! hg.topre_Pairing_condition (Classical.choose hxs)).1
            if other ∈ hist
            then spam
            else other
          else
            spam
    | [] => spam




noncomputable
def Pairing_fStrat [DecidableEq α] [Fintype α] {win_sets : Finset (Finset α)} {g : Positional_Game_World win_sets} (hg : Pairing_condition g) :
  fStrategy g.init_game_state g.fst_legal g.snd_legal :=
  fun hist T leg =>
    ⟨ Pairing_StratCore hg hist leg,
      (by
       sorry
       )
      ⟩



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
