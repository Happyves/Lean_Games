/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Tactic

lemma Classical.choose_congr {P Q : α → Prop} (a : ∃ p, P p) (b : ∃ q, Q q) (h : ∀ x, P x ↔ Q x) : Classical.choose a = Classical.choose b :=
  by congr ; funext x ; rw [h]

lemma Classical.choose_congr_surgery {S1 S2 : α → Prop} {P : {x : α // S1 x} → Prop} {Q : {x : α // S2 x} → Prop} {a : ∃ p, P p} {b : ∃ q, Q q}
  {P' Q' : α → Prop} (hp : ∀ x, P x = P' x.val) (hq : ∀ x, Q x = Q' x.val) (hs : ∀ x, S1 x ↔ S2 x)  (h : ∀ x, P' x ↔ Q' x) :
  (Classical.choose a).val = (Classical.choose b).val :=
  by
  have : (Classical.choose a).val = (Classical.choose a).val := rfl
  convert this using 4
  · funext _
    apply propext
    rw [hs]
  · rename_i x y heq
    rw [Subtype.heq_iff_coe_eq (by intro _ ; rw [hs])] at heq
    rw [hp,hq, heq, h]
