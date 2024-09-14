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
