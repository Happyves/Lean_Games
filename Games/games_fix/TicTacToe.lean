/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib_fixfix.Pairing
import Games.games_fix.TTT_CombinatorialLines




variable (D n : ℕ)

variable (hn : 1 < n)

open Classical

noncomputable
def TTT_win_sets : Finset (Finset (Fin D → Fin n)) := Finset.univ.filter (is_combi_line D n (strengthen n hn))

noncomputable
def TTT := Positional_Game_World (TTT_win_sets D n hn)

#check incidence_ub

#check  Finset.all_card_le_biUnion_card_iff_existsInjective'
#check Fintype.all_card_le_rel_image_card_iff_exists_injective

#check Finset.biUnion


noncomputable
instance : Finite ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) := by infer_instance

noncomputable
instance : Fintype ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) := by infer_instance


def line_set_neighbours (l : {c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool): Finset (Fin D → Fin n) :=
  Finset.univ.filter (fun p => p ∈ l.1.val)

noncomputable
def point_neighbours (p : Fin D → Fin n): Finset ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) :=
  Finset.univ.filter (fun l => p ∈ l.1.val)

def line_point_rel (l : {c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) (p : Fin D → Fin n) : Prop  := p ∈ l.1.val

#check Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow

lemma double_count_line_points (ls : Finset ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool)) :
  (Finset.sum ls (fun a => (Finset.bipartiteAbove (line_point_rel D n hn) (Finset.biUnion ls (line_set_neighbours D n hn)) a).card)) =
  Finset.sum (Finset.biUnion ls (line_set_neighbours D n hn)) (fun b => (Finset.bipartiteBelow (line_point_rel D n hn) ls b).card) :=
  @Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _ _  (line_point_rel D n hn) ls (Finset.biUnion ls (line_set_neighbours D n hn)) _


lemma line_has_n_points (ls : Finset ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool)) (a : {c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) (ha : a ∈ ls) :
  (Finset.bipartiteAbove (line_point_rel D n hn) (Finset.biUnion ls (line_set_neighbours D n hn)) a).card = n :=
  by
  dsimp [Finset.bipartiteAbove]
  have : Finset.filter (line_point_rel D n hn a) (Finset.biUnion ls (line_set_neighbours D n hn)) = Finset.univ.filter (fun p => p ∈ a.1.val) :=
    by
    ext x
    simp_rw [Finset.mem_filter]
    rw [Finset.mem_biUnion, line_point_rel]
    constructor
    · rintro ⟨_,m⟩
      exact ⟨Finset.mem_univ _, m⟩
    · rintro ⟨_,m⟩
      constructor
      · use a
        rw [line_set_neighbours, Finset.mem_filter]
        exact ⟨ha, Finset.mem_univ _, m⟩
      · exact m
  rw [this]
  clear this
  obtain ⟨s,sdef, sim⟩ := a.1.prop
  rw [sim, Finset.filter_mem_image_eq_image _ _ _ (fun _ _ => Finset.mem_univ _)]
  simp_rw [← Finset.card_fin n, Finset.card_image_iff]
  apply seq_inj D n hn s sdef

#check Finset.card_image_iff

#check Finset.card_fin

-- to mathlib ?
lemma Finset.card_filter_le_card_filter_univ [Fintype α ]
  {s : Finset α} {p : α → Prop} [DecidablePred p] : (s.filter p).card ≤ (Finset.univ.filter p).card :=
  by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact subset_univ s

lemma point_inicdence_ub (ls : Finset ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool)) (p : Fin D → Fin n) :
  (Finset.bipartiteBelow (line_point_rel D n hn) ls p).card ≤ (3^D - 1) :=
  by
  apply le_trans _ (Nat.mul_div_le _ 2)
  have : (Finset.bipartiteBelow (line_point_rel D n hn) ls p).card ≤ ((Finset.univ : Finset Bool) ×ˢ (Finset.filter (fun c => is_combi_line D n (strengthen n hn) c ∧ p ∈ c) Finset.univ)).card :=
    by
    apply le_trans (Finset.card_filter_le_card_filter_univ)
    apply Finset.card_le_card_of_inj_on (fun x : ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) => (x.2, x.1.val))
    · simp_rw [Finset.mem_filter, Finset.mem_product,Finset.mem_filter]
      rintro a ⟨ _, h ⟩
      refine' ⟨Finset.mem_univ _, Finset.mem_univ _, _ ⟩
      constructor
      · exact a.1.prop
      · apply h
    · intro a _ b _ main
      rw [Prod.eq_iff_fst_eq_snd_eq]
      simp_rw [Prod.eq_iff_fst_eq_snd_eq] at main
      exact ⟨Subtype.eq main.2, main.1⟩
  apply le_trans this
  rw [Finset.card_product, Finset.card_univ,  Fintype.card_bool]
  apply Nat.mul_le_mul_left
  apply incidence_ub D n hn


#check Nat.mul_div_le
#check Fintype.card_bool
#check Finset.card_product
#check Nat.mul_le_mul

#check le_of_mul_le_mul_right


lemma main_bound (ls : Finset ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool)) :  ls.card * n ≤ (Finset.biUnion ls (line_set_neighbours D n hn)).card * (3^D - 1) :=
  by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  have := double_count_line_points D n hn ls
  have L : (Finset.sum ls fun a => (Finset.bipartiteAbove (line_point_rel D n hn) (Finset.biUnion ls (line_set_neighbours D n hn)) a).card) = (Finset.sum ls fun _ => n) :=
    by
    apply Finset.sum_congr rfl (fun x hx => line_has_n_points D n hn ls x hx)
  have R : Finset.sum (Finset.biUnion ls (line_set_neighbours D n hn)) (fun b => (Finset.bipartiteBelow (line_point_rel D n hn) ls b).card) ≤ Finset.sum (Finset.biUnion ls (line_set_neighbours D n hn)) (fun x => 3 ^ D - 1) :=
    by
    apply Finset.sum_le_sum
    intro a _
    apply point_inicdence_ub
  apply le_trans _ R
  rw [← L]
  apply le_of_eq
  exact this


#eval (Finset.univ : Finset (Fin 0 → Fin 0)).card


lemma Hall_condition (ls : Finset ({c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool))
  (h : n ≥ 3^D - 1) :
  ls.card ≤ (Finset.biUnion ls (line_set_neighbours D n hn)).card :=
  by
  have := main_bound D n hn ls
  apply Nat.le_of_mul_le_mul_left _ (show 0 < n by apply lt_trans _ hn ; exact Nat.one_pos)
  rw [mul_comm]
  apply le_trans this
  rw [mul_comm]
  apply Nat.mul_le_mul_right
  exact h


#check  Finset.all_card_le_biUnion_card_iff_existsInjective'

variable (h : n ≥ 3^D - 1)

noncomputable
def TTT_pairing  :=
  Classical.choose ((Finset.all_card_le_biUnion_card_iff_existsInjective' (line_set_neighbours D n hn)).mp (fun ls => Hall_condition D n hn ls h))

lemma TTT_pairing_inj : Function.Injective (TTT_pairing D n hn h) :=
  (Classical.choose_spec ((Finset.all_card_le_biUnion_card_iff_existsInjective' (line_set_neighbours D n hn)).mp (fun ls => Hall_condition D n hn ls h))).1

lemma TTT_pairing_map (l : { c // is_combi_line D n (strengthen n hn) c } × Bool) :
  (TTT_pairing D n hn h) l ∈ (line_set_neighbours D n hn) l :=
  (Classical.choose_spec ((Finset.all_card_le_biUnion_card_iff_existsInjective' (line_set_neighbours D n hn)).mp (fun ls => Hall_condition D n hn ls h))).2 l


lemma line_set_neighbours_is_line (l : {c : Finset (Fin D → Fin n) // is_combi_line D n (strengthen n hn) c} × Bool) :
  line_set_neighbours D n hn l = l.1.val :=
  by
  dsimp [line_set_neighbours]
  rw [Finset.filter_univ_mem]



lemma TTT_pre_Pairing_condition : pre_Pairing_condition (TTT_win_sets D n hn) :=
  by
  rw [TTT_win_sets]
  intro w
  let w_dtt_pain := (⟨w.val, by have wp := w.prop ; simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at wp ; exact wp ⟩ : {x // is_combi_line D n (strengthen n hn) x})
  use (TTT_pairing D n hn h (w_dtt_pain, true), TTT_pairing D n hn h (w_dtt_pain, false))
  constructor
  · dsimp
    intro con
    have := TTT_pairing_inj D n hn h con
    simp_rw [Prod.eq_iff_fst_eq_snd_eq] at this
    exact this.2
  · dsimp
    have := TTT_pairing_map D n hn h (w_dtt_pain, true)
    rw [line_set_neighbours_is_line] at this
    apply this
    -- creates shit-show if w_dtt_pain isn't used
  · dsimp
    have := TTT_pairing_map D n hn h (w_dtt_pain, false)
    rw [line_set_neighbours_is_line] at this
    apply this


lemma TTT_Pairing_condition : Pairing_condition (TTT_win_sets D n hn) :=
  by
  constructor
  · intro w v wnv
    have := pairing_prop (TTT_pre_Pairing_condition D n hn h)
    constructor
    ·
  · exact TTT_pre_Pairing_condition D n hn h
