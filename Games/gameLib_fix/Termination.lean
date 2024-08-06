
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


def State_from_history_neutral (ini : α ) (f_trans s_trans : α → List β → (β → α)) (f_wins s_wins : α → Prop) (hist : List β) : Prop :=
  (¬ (f_wins (State_from_history ini f_trans s_trans hist))) ∧ (¬ (s_wins (State_from_history ini f_trans s_trans hist)))



def Game_World.state_on_turn_neutral (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) : Prop :=
  (¬ (g.fst_win_states (g.state_on_turn f_strat s_strat turn))) ∧ (¬ (g.snd_win_states (g.state_on_turn f_strat s_strat turn)))

def Symm_Game_World.state_on_turn_neutral (g : Symm_Game_World α β)
  (f_strat : fStrategy g.init_game_state g.law g.law)
  (s_strat : sStrategy g.init_game_state g.law g.law) (turn : ℕ) : Prop :=
  Game_World.state_on_turn_neutral (g.toGame_World) f_strat s_strat turn

def Game.state_on_turn_neutral (g : Game α β) (turn : ℕ) : Prop :=
  g.toGame_World.state_on_turn_neutral g.fst_strat g.snd_strat turn

def Symm_Game.state_on_turn_neutral (g : Symm_Game α β) (turn : ℕ) : Prop :=
  g.toGame.state_on_turn_neutral turn


lemma Game_World.state_on_turn_neutral_State_from_history_neutral (g : Game_World α β)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal)
  (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (turn : ℕ) :
  g.state_on_turn_neutral f_strat s_strat turn ↔
  State_from_history_neutral g.init_game_state g.fst_transition g.snd_transition g.fst_win_states g.snd_win_states
  (History_on_turn g.init_game_state g.fst_legal g.snd_legal f_strat s_strat turn).val :=
  by
  dsimp [Game_World.state_on_turn_neutral, State_from_history_neutral]
  rw [Game_World.state_on_turn_State_from_history]


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
  ∃ ws : sStrategy g.init_game_state g.fst_legal g.snd_legal,
  ∀ fst_s : fStrategy g.init_game_state g.fst_legal g.snd_legal,
  ({g with fst_strat := fst_s, snd_strat := ws} : Game α β).snd_win

def Symm_Game_World.is_fst_win  {α β : Type _} (g : Symm_Game_World α β) : Prop :=
  g.toGame_World.is_fst_win

def Symm_Game_World.is_snd_win  {α β : Type _} (g : Symm_Game_World α β) : Prop :=
  g.toGame_World.is_snd_win

inductive Game_World.has_WL (g : Game_World α β) : Prop where
| wf (h : g.is_fst_win)
| ws (h : g.is_snd_win)

def Symm_Game_World.has_WL (g : Symm_Game_World α β) := g.toGame_World.has_WL



-- # Coherent end

structure Game_World.coherent_end (g : Game_World α β) : Prop where
  fst : ∀ hist, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → (g.fst_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition hist) →
          ∀ act, ((Turn_fst (hist.length+1) → g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (hist.length+1) → g.snd_legal g.init_game_state hist act)) →
            g.fst_win_states ((State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist))))
  snd : ∀ hist, Hist_legal g.init_game_state g.fst_legal g.snd_legal hist → (g.snd_win_states (State_from_history g.init_game_state g.fst_transition g.snd_transition hist) →
          ∀ act, ((Turn_fst (hist.length+1) → g.fst_legal g.init_game_state hist act) ∧ (Turn_snd (hist.length+1) → g.snd_legal g.init_game_state hist act)) →
            g.snd_win_states ((State_from_history g.init_game_state g.fst_transition g.snd_transition (act :: hist))))




-- TODO : Refactor ↓
#exit

def Game_World.coherent_end (g : Game_World α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (t : ℕ),
    (g.fst_win_states (g.state_on_turn f_strat s_strat t) → g.fst_win_states (g.state_on_turn f_strat s_strat (t+1))) ∧
      (g.snd_win_states (g.state_on_turn f_strat s_strat t) → g.snd_win_states (g.state_on_turn f_strat s_strat (t+1)))


lemma Game_World.coherent_end_all (g : Game_World α β)  (h : g.coherent_end)
  (f_strat : fStrategy g.init_game_state g.fst_legal g.snd_legal) (s_strat : sStrategy g.init_game_state g.fst_legal g.snd_legal) (t n : ℕ) :
  (g.fst_win_states (g.state_on_turn f_strat s_strat t) → g.fst_win_states (g.state_on_turn f_strat s_strat (t+n))) ∧
    (g.snd_win_states (g.state_on_turn f_strat s_strat t) → g.snd_win_states (g.state_on_turn f_strat s_strat (t+n))) :=
  by
  constructor
  · intro H
    induction' n with n ih
    · dsimp
      exact H
    · apply (h f_strat s_strat (t+n)).1
      exact ih
  · intro H
    induction' n with n ih
    · dsimp
      exact H
    · apply (h f_strat s_strat (t+n)).2
      exact ih


def Symm_Game_World.coherent_end (g : Symm_Game_World α β) : Prop :=
  ∀ (f_strat : fStrategy g.init_game_state g.law g.law) (s_strat : sStrategy g.init_game_state g.law g.law) (t : ℕ),
    g.win_states (g.state_on_turn f_strat s_strat t) → g.win_states (g.state_on_turn f_strat s_strat (t+1))


lemma Symm_Game_World.coherent_end_all (g : Symm_Game_World α β)  (h : g.coherent_end)
  (f_strat : fStrategy g.init_game_state g.law g.law) (s_strat : sStrategy g.init_game_state g.law g.law) (t n : ℕ) :
  g.win_states (g.state_on_turn f_strat s_strat t) → g.win_states (g.state_on_turn f_strat s_strat (t+n)) :=
  by
  intro H
  induction' n with n ih
  · dsimp
    exact H
  · apply h _ _
    exact ih
