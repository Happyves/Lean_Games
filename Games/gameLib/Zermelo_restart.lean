/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic
import Mathlib.Tactic



lemma Game_World.must_terminate_before_zero {α β : Type u}
  (g : Game_World α β) :
  g.must_terminate_before 0 ↔ (∀ act : β, ¬ (g.snd_legal [] act)) :=
  by
  dsimp [must_terminate_before]
  sorry

#exit

lemma Game_World.conditioning {α β : Type u}
  (g : Game_World α β)
  {T : ℕ} (hg : g.must_terminate_before T)
  {P : Game_World α β → Prop}
  (base : ∀ (g' : Game_World α β), g'.must_terminate_before 0 → P g')
  (step : ∀ (g' : Game_World α β), ∀ t : ℕ, (g'.must_terminate_before t → P g') → (g'.must_terminate_before (t+1) → P g')):
  P g :=
  by
