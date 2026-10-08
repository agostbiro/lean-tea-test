import Dungeon.Core.Check

/-! # Game rules and the move-preservation theorem.

`State.step` is the whole rule set: four directional steps plus wait. The
theorem `State.step_inv` says every step preserves the invariant, and `Game`
packages a state with its invariant so the headline result holds by
construction for every state the game can ever be in. -/

namespace Crawl

/-- A stationary creature with hit points. -/
structure Monster where
  pos : Pos
  hp : Nat
  deriving Repr, Inhabited, DecidableEq

/-- The full rules-level state of one dungeon run. -/
structure State where
  dungeon : Dungeon
  player : Pos
  held : Held
  hp : Nat
  monsters : List Monster
  deriving Repr, Inhabited

/-- What the player can do in one turn. -/
inductive Move where
  | step (d : Dir)
  | wait
  deriving Repr, DecidableEq, Inhabited

/-- What happened, for the message line. Not part of any theorem. -/
inductive Event where
  | waited
  | moved
  | blocked
  | lockedDoor (c : Color)
  | openedDoor (c : Color)
  | pickedKey (c : Color)
  | reachedStairs
  | hitMonster (remaining : Nat)
  | killedMonster
  deriving Repr, DecidableEq, Inhabited

/-- Damage the player deals per attack. -/
def playerDamage : Nat := 1
/-- Damage a monster deals when it strikes back. -/
def monsterDamage : Nat := 1

def State.monsterAt (s : State) (p : Pos) : Option Monster :=
  s.monsters.find? (·.pos = p)

/-- Bumping a monster: it loses hit points, and strikes back if it survives. -/
def State.attack (s : State) (m : Monster) : State × Event :=
  if m.hp ≤ playerDamage then
    ({ s with monsters := s.monsters.filter (·.pos ≠ m.pos) }, .killedMonster)
  else
    ({ s with
        monsters := s.monsters.map fun n =>
          if n.pos = m.pos then { n with hp := n.hp - playerDamage } else n
        hp := s.hp - monsterDamage },
      .hitMonster (m.hp - playerDamage))

/-- Entering a passable cell, picking up whatever key lies there. -/
def State.moveTo (s : State) (q : Pos) : State × Event :=
  let cell := s.dungeon.cellAt q
  ({ s with player := q, held := cell.pickUp s.held },
    match cell with
    | .key c => .pickedKey c
    | .door c => .openedDoor c
    | .stairs => .reachedStairs
    | _ => .moved)

/-- The rules. -/
def State.step (s : State) : Move → State × Event
  | .wait => (s, .waited)
  | .step d =>
    match s.player.move d with
    | none => (s, .blocked)
    | some q =>
      match s.monsterAt q with
      | some m => s.attack m
      | none =>
        if (s.dungeon.cellAt q).passable s.held then s.moveTo q
        else
          match s.dungeon.cellAt q with
          | .door c => (s, .lockedDoor c)
          | _ => (s, .blocked)

/-- The invariant every game state satisfies: the player stands on a cell they
could enter, and the Stairs are reachable. -/
def State.Inv (s : State) : Prop :=
  StandOk s.dungeon s.held s.player ∧ Completable s.dungeon s.player s.held

theorem State.attack_inv {s : State} {m : Monster} (h : s.Inv) : (s.attack m).1.Inv := by
  unfold State.attack
  split <;> exact h

theorem State.moveTo_inv {s : State} {q : Pos} (h : s.Inv) (hadj : Adj s.player q)
    (hpass : (s.dungeon.cellAt q).passable s.held) : (s.moveTo q).1.Inv :=
  ⟨Cell.passable_mono (Cell.subset_pickUp _ _) hpass,
    (h.2.rebase_adj hadj h.1).mono (Cell.subset_pickUp _ _)⟩

/-- **Move preservation.** Every legal move keeps the invariant. -/
theorem State.step_inv (s : State) (m : Move) (h : s.Inv) : (s.step m).1.Inv := by
  cases m with
  | wait => exact h
  | step d =>
    simp only [State.step]
    split
    · exact h
    · rename_i q hq
      split
      · exact State.attack_inv h
      · split
        · rename_i hpass
          exact State.moveTo_inv h (Pos.move_adj hq) hpass
        · split <;> exact h

/-- A state together with the proof that it satisfies the invariant. Every
value of this type is Completable, so the game can never be softlocked. -/
structure Game where
  state : State
  inv : state.Inv

def Game.step (g : Game) (m : Move) : Game × Event :=
  (⟨(g.state.step m).1, g.state.step_inv m g.inv⟩, (g.state.step m).2)

/-- Start a game if the checker accepts the dungeon and the player stands on an
open cell. -/
def Game.start? (d : Dungeon) (player : Pos) (hp : Nat) (monsters : List Monster) :
    Option Game :=
  if h : check d player [] = true ∧ (d.cellAt player).passable [] then
    some ⟨{ dungeon := d, player := player, held := [], hp := hp, monsters := monsters },
      ⟨h.2, check_sound h.1⟩⟩
  else none

/-- **No softlock.** Whatever state the game is in, the Stairs are reachable. -/
theorem Game.completable (g : Game) :
    Completable g.state.dungeon g.state.player g.state.held :=
  g.inv.2

theorem Game.step_completable (g : Game) (m : Move) :
    Completable (g.step m).1.state.dungeon (g.step m).1.state.player (g.step m).1.state.held :=
  (g.step m).1.completable

def Game.won (g : Game) : Bool := g.state.dungeon.cellAt g.state.player = .stairs
def Game.dead (g : Game) : Bool := g.state.hp = 0

end Crawl
