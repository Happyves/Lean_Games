
# Combinatorial and positional games in Lean

Welcome to formal combinatorial and positional game theory in Lean !
We formalize content from:
- Deborah Kent and Matt De Vos. "Game theory: a playful introduction", American Mathematical Society, 2017.
- Hefetz, D., Krivelevich, M., Stojaković, M., & Szabó, T. (2014). "Positional games" (Vol. 44). Basel: Birkhäuser.


# Current state of the project

Still a work in progress, though in its final phase.
I'm currently:
- Cleaning the content.
- Experimenting with strategies that condition on histories being neutral, in `gameLibExp` and `gameLibExpExp`
- Documenting the code

Once finished, I will bring the project to the latest version of mathlib, and attempt to publish this work :)

Known related work:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Game/Basic.html
- https://www.isa-afp.org/entries/GaleStewart_Games.html

Please let me know if you're aware of more related work


# Roadmap for reading

- Start by reading `gameLib > Basic` and `gameLib > Termination`. To see the objects we define there in action, we suggest reading `games > PickUpBricks` on the side, or right after.

- To understand `gameLib > Zermelo`, you should check out `gameLib > StrategyAPI`, `gameLib > HistoryMoves` and `exLib > General`.

- Strategy stealing is defined in `gameLib > Stealing`, and it is based on `gameLib > Zermelo`. We apply it on the game of Chomp, in `games > Chomp`. 

- Positional games are defined in `gameLib > Positional`. They allow for a special type of strategies, described in `gameLib > Pairing`. We apply them on the game of high dimensional Tic-tac-toe, in `games > TicTacToe`, which is based on the notion of a combinatorial line, described in `games > TTT_CombinatorialLines`.