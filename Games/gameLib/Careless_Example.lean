/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Games.gameLib.Zermelo
import Games.games.PickUpBricks

def careful_strat (ini : ℕ) (hist : List ℕ) :=
  if bricks_start_turn_from_ini_hist ini hist = 0
  then 0
  else if hist = []
       then 1
       else 2


#eval History_on_turn 10 toy_strat careful_strat 10
-- recall that toy strat always takes 1 brick
#eval (History_on_turn 9 careful_strat toy_strat 9) ++ [toy_strat 10 []]
-- the histories are different


def careful_strat' (ini : ℕ) (hist : List ℕ) :=
  if bricks_start_turn_from_ini_hist ini hist = 0
  then 0
  else if hist.length < 3
       then 1
       else 2


#eval History_on_turn 10 toy_strat careful_strat' 10
-- The histories coincide for the first few turn, but are differ later on
#eval (History_on_turn 9 careful_strat' toy_strat 10) ++ [toy_strat 10 []]
