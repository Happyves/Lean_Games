
import Games.gameLib_fix.Basic


inductive Game_World.Turn_isWL (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop where
| wf : Turn_fst turn → g.fst_win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn
| ws : Turn_snd turn → g.snd_win_states (g.state_on_turn f_strat s_strat turn) → g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.Turn_isWL (g : Symm_Game_World α β)
  (f_strat : fStrategy g.init_game_state g.law g.law)
  (s_strat : sStrategy g.init_game_state g.law g.law) (turn : ℕ) : Prop :=
  --g.win_states (g.state_on_turn f_strat s_strat turn)
  Game_World.Turn_isWL (g.toGame_World) f_strat s_strat turn


def Game_World.isWL (g : Game_World α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∃ turn, g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.isWL (g : Symm_Game_World α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.law g.law),
  ∀ (s_strat : sStrategy g.init_game_state g.law g.law),
  ∃ turn, g.Turn_isWL f_strat s_strat turn

def Game_World.isWL_wBound (g : Game_World α β) (T : ℕ): Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∀ (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal),
  ∃ turn ≤ T, g.Turn_isWL f_strat s_strat turn


def Symm_Game_World.isWL_wBound (g : Symm_Game_World α β) (T : ℕ): Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.law g.law),
  ∀ (s_strat : sStrategy g.init_game_state g.law g.law),
  ∃ turn ≤ T, g.Turn_isWL f_strat s_strat turn


def Game_World.state_on_turn_neutral (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop :=
  if Turn_fst turn
  then ¬ (g.fst_win_states (g.state_on_turn f_strat s_strat turn))
  else ¬ (g.snd_win_states (g.state_on_turn f_strat s_strat turn))

def Symm_Game_World.state_on_turn_neutral (g : Symm_Game_World α β)
  (f_strat : fStrategy g.init_game_state g.law g.law)
  (s_strat : sStrategy g.init_game_state g.law g.law) (turn : ℕ) : Prop :=
  Game_World.state_on_turn_neutral (g.toGame_World) f_strat s_strat turn

def Game.state_on_turn_neutral (g : Game α β) (turn : ℕ) : Prop :=
  g.toGame_World.state_on_turn_neutral g.fst_strat g.snd_strat turn

def Symm_Game.state_on_turn_neutral (g : Symm_Game α β) (turn : ℕ) : Prop :=
  g.toGame.state_on_turn_neutral turn

def Game.fst_win  {α β : Type _} (g : Game α β) : Prop :=
  ∃ turn : ℕ, Turn_fst turn ∧ g.fst_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Game.snd_win  {α β : Type _} (g : Game α β) : Prop :=
  ∃ turn : ℕ, Turn_snd turn  ∧ g.snd_win_states (g.state_on_turn turn) ∧
    (∀ t < turn, g.state_on_turn_neutral t)

def Symm_Game.fst_win  {α β : Type _} (g : Symm_Game α β) : Prop :=
  g.toGame.fst_win

def Symm_Game.snd_win  {α β : Type _} (g : Symm_Game α β) : Prop :=
  g.toGame.snd_win

def Game_World.is_fst_win  {α β : Type _} (g : Game_World α β) : Prop :=
  ∃ ws : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ snd_s : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game α β).fst_win

def Game_World.is_snd_win  {α β : Type _} (g : Game_World α β) : Prop :=
  ∃ ws : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ snd_s : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := ws, snd_strat := snd_s} : Game α β).snd_win

def Symm_Game_World.is_fst_win  {α β : Type _} (g : Symm_Game_World α β) : Prop :=
  g.toGame_World.is_fst_win

def Symm_Game_World.is_snd_win  {α β : Type _} (g : Symm_Game_World α β) : Prop :=
  g.toGame_World.is_snd_win

inductive Game_World.has_WL (g : Game_World α β) : Prop where
| wf (h : g.is_fst_win)
| ws (h : g.is_snd_win)

def Symm_Game_World.has_WL (g : Symm_Game_World α β) := g.toGame_World.has_WL
