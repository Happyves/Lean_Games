/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Basic



-- # Strategies

def Game_World.cfStrategy (g : Game_World α β) :=
  (hist : List β) → (Turn_fst (hist.length+1)) →
  (g.hist_legal hist) → (g.hist_neutral hist) →
  { act : β // g.fst_legal hist act}

def Game_World.csStrategy (g : Game_World α β) :=
  (hist : List β) → (Turn_snd (hist.length+1)) →
  (g.hist_legal hist) → (g.hist_neutral hist) →
  { act : β // g.snd_legal hist act}

def Game_World_wDraw.cfStrategy (g : Game_World_wDraw α β) :=
  g.toGame_World.fStrategy

def Game_World_wDraw.csStrategy (g : Game_World_wDraw α β) :=
  g.toGame_World.sStrategy

def Symm_Game_World.cfStrategy (g : Symm_Game_World α β) :=
  g.toGame_World.fStrategy

def Symm_Game_World.csStrategy (g : Symm_Game_World α β) :=
  g.toGame_World.sStrategy
