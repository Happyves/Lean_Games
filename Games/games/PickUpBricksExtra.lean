


/-
Pick-up-bricks, but the first player may take 3 bricks at most once in the game.

Then fst player have win strat: if bricks div by 3, take 3, then play with usual win strat ;
if bricks not div by 3, play usual win strat.

The point is that this game is not entirely state dependent. Since the first player can play a
specific move only once, the fst_legal function can not depend only on the current state, but
requires the history.

Good for illustrating expressivity of my formalism.

-/
