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

/-- The full rules-level state of one dungeon run. The dungeon grid never
changes; `got` and `opened` record the key cells emptied and doors opened. -/
structure State where
  dungeon : Dungeon
  player : Pos
  got : List Pos
  opened : List Pos
  hp : Nat
  monsters : List Monster
  deriving Repr, Inhabited

/-- The part of the state the theorem is about. -/
def State.config (s : State) : Config := ⟨s.player, s.got, s.opened⟩

/-- Keys of a color in hand. -/
def State.held (s : State) (c : Color) : Nat := s.config.held s.dungeon c

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
  | wouldStrand (c : Color)
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

/-- Walking onto a cell that needs no key and holds none. -/
def State.walkTo (s : State) (q : Pos) : State × Event :=
  ({ s with player := q }, if s.dungeon.cellAt q = .stairs then .reachedStairs else .moved)

/-- Picking up the key on `q`. -/
def State.pickUp (s : State) (q : Pos) (c : Color) : State × Event :=
  ({ s with player := q, got := q :: s.got }, .pickedKey c)

/-- Spending a key on the door at `q`. Refused when the checker cannot find the
Stairs afterwards, so a key is never wasted on the wrong door. -/
def State.unlock (s : State) (q : Pos) (c : Color) : State × Event :=
  if check s.dungeon ⟨q, s.got, q :: s.opened⟩ then
    ({ s with player := q, opened := q :: s.opened }, .openedDoor c)
  else (s, .wouldStrand c)

/-- Trying to enter the cell `q`, which holds no monster. -/
def State.enter (s : State) (q : Pos) : State × Event :=
  if s.config.free s.dungeon q then s.walkTo q
  else
    match s.dungeon.cellAt q with
    | .key c => s.pickUp q c
    | .door c => if 0 < s.held c then s.unlock q c else (s, .lockedDoor c)
    | _ => (s, .blocked)

/-- The rules. -/
def State.step (s : State) : Move → State × Event
  | .wait => (s, .waited)
  | .step d =>
    match s.player.move d with
    | none => (s, .blocked)
    | some q =>
      match s.monsterAt q with
      | some m => s.attack m
      | none => s.enter q

/-- The invariant every game state satisfies: the player stands on a cell they
can walk back onto, no key cell is counted twice, and the Stairs are reachable. -/
def State.Inv (s : State) : Prop :=
  StandOk s.dungeon s.config ∧ s.got.Nodup ∧ Completable s.dungeon s.config

theorem State.attack_inv {s : State} {m : Monster} (h : s.Inv) : (s.attack m).1.Inv := by
  unfold State.attack
  split <;> exact h

theorem State.walkTo_inv {s : State} {q : Pos} (h : s.Inv) (hadj : Adj s.player q)
    (hq : s.config.free s.dungeon q = true) : (s.walkTo q).1.Inv :=
  ⟨hq, h.2.1, h.2.2.back hadj.symm h.1⟩

theorem State.pickUp_inv {s : State} {q : Pos} {c : Color} (h : s.Inv) (hadj : Adj s.player q)
    (hq : s.dungeon.cellAt q = .key c) (hn : q ∉ s.got) : (s.pickUp q c).1.Inv := by
  refine ⟨?_, List.nodup_cons.2 ⟨hn, h.2.1⟩, ?_⟩
  · simp [StandOk, State.pickUp, State.config, Config.free, hq]
  · exact Completable.ahead (a := ⟨q, s.got, s.opened⟩)
      ⟨rfl, rfl, List.subset_cons_self _ _, h.2.1⟩ (h.2.2.back hadj.symm h.1)

theorem State.unlock_inv {s : State} {q : Pos} {c : Color} (h : s.Inv)
    (hq : s.dungeon.cellAt q = .door c) : (s.unlock q c).1.Inv := by
  unfold State.unlock
  split
  · rename_i hc
    refine ⟨?_, h.2.1, check_sound hc⟩
    simp [StandOk, State.config, Config.free, hq]
  · exact h

theorem State.enter_inv {s : State} {q : Pos} (h : s.Inv) (hadj : Adj s.player q) :
    (s.enter q).1.Inv := by
  unfold State.enter
  split
  · rename_i hf
    exact State.walkTo_inv h hadj hf
  · rename_i hf
    split
    · rename_i c hc
      simp [State.config, Config.free, hc] at hf
      exact State.pickUp_inv h hadj hc hf
    · rename_i c hc
      split
      · exact State.unlock_inv h hc
      · exact h
    · exact h

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
      · exact State.enter_inv h (Pos.move_adj hq)

/-- A state together with the proof that it satisfies the invariant. Every
value of this type is Completable, so the game can never be softlocked. -/
structure Game where
  state : State
  inv : state.Inv

def Game.step (g : Game) (m : Move) : Game × Event :=
  (⟨(g.state.step m).1, g.state.step_inv m g.inv⟩, (g.state.step m).2)

/-- Start a game if the checker accepts the dungeon and the player stands on an
cell they can stand on. -/
def Game.start? (d : Dungeon) (player : Pos) (hp : Nat) (monsters : List Monster) :
    Option Game :=
  if h : check d ⟨player, [], []⟩ = true ∧ StandOk d ⟨player, [], []⟩ then
    some ⟨{ dungeon := d, player := player, got := [], opened := [], hp := hp, monsters },
      ⟨h.2, List.nodup_nil, check_sound h.1⟩⟩
  else none

/-- **No softlock.** Whatever state the game is in, the Stairs are reachable. -/
theorem Game.completable (g : Game) : Completable g.state.dungeon g.state.config :=
  g.inv.2.2

theorem Game.step_completable (g : Game) (m : Move) :
    Completable (g.step m).1.state.dungeon (g.step m).1.state.config :=
  (g.step m).1.completable

def Game.won (g : Game) : Bool := g.state.dungeon.cellAt g.state.player = .stairs
def Game.dead (g : Game) : Bool := g.state.hp = 0

end Crawl
