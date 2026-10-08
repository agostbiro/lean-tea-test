import Dungeon.Core

/-! # Dungeon generation.

Unproven code, by design (see `docs/adr/0001`). The generator proposes, the
checker in `Dungeon.Core` decides. Generation is pure given a seed, so it can
run inside the TUI's pure update loop. -/

namespace Crawl.Gen

def width : Nat := 60
def height : Nat := 20
def playerHp : Nat := 10
def monsterHp : Nat := 3
def monsterCount : Nat := 4
def roomTarget : Nat := 7
def roomAttempts : Nat := 60
/-- Rolls before giving up and using the fallback. -/
def budget : Nat := 50

abbrev Rand := StateM StdGen

def rnd (lo hi : Nat) : Rand Nat := fun g => randNat g lo hi

def pick (xs : List α) [Inhabited α] : Rand α := do
  let i ← rnd 0 (xs.length - 1)
  return xs[i]!

def coin : Rand Bool := do return (← rnd 0 1) = 1

/-- A room's interior: cells `[x, x + w) × [y, y + h)`. -/
structure Room where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Repr, Inhabited

def Room.center (r : Room) : Pos := ⟨r.x + r.w / 2, r.y + r.h / 2⟩

def Room.contains (r : Room) (p : Pos) : Bool :=
  r.x ≤ p.x ∧ p.x < r.x + r.w ∧ r.y ≤ p.y ∧ p.y < r.y + r.h

/-- Interiors must be separated by at least two wall cells so a corridor can
carry a door between them. -/
def Room.tooClose (a b : Room) : Bool :=
  a.x < b.x + b.w + 2 ∧ b.x < a.x + a.w + 2 ∧ a.y < b.y + b.h + 2 ∧ b.y < a.y + a.h + 2

def Room.cells (r : Room) : List Pos :=
  (List.range r.h).flatMap fun dy => (List.range r.w).map fun dx => ⟨r.x + dx, r.y + dy⟩

def index (p : Pos) : Nat := p.y * width + p.x

def carve (cells : Array Cell) (p : Pos) (c : Cell) : Array Cell :=
  cells.set! (index p) c

def placeRooms : Rand (List Room) := do
  let mut rooms : List Room := []
  for _ in [:roomAttempts] do
    if rooms.length ≥ roomTarget then break
    let w ← rnd 4 9
    let h ← rnd 3 5
    let x ← rnd 1 (width - w - 2)
    let y ← rnd 1 (height - h - 2)
    let r : Room := ⟨x, y, w, h⟩
    if rooms.all (fun o => !o.tooClose r) then
      rooms := rooms ++ [r]
  return rooms

/-- Cells of an L-shaped corridor from `a` to `b`, in walking order. -/
def corridor (a b : Pos) (horizontalFirst : Bool) : List Pos :=
  let xs := if a.x ≤ b.x then List.range' a.x (b.x - a.x + 1)
            else (List.range' b.x (a.x - b.x + 1)).reverse
  let ys := if a.y ≤ b.y then List.range' a.y (b.y - a.y + 1)
            else (List.range' b.y (a.y - b.y + 1)).reverse
  if horizontalFirst then
    xs.map (fun x => ⟨x, a.y⟩) ++ ys.map (fun y => ⟨b.x, y⟩)
  else
    ys.map (fun y => ⟨a.x, y⟩) ++ xs.map (fun x => ⟨x, b.y⟩)

/-- The corridor cell just before the path first enters `room`, if that cell
lies outside every room. -/
def doorSpot (path : List Pos) (room : Room) (rooms : List Room) : Option Pos :=
  let rec go : List Pos → Option Pos → Option Pos
    | [], _ => none
    | p :: rest, prev =>
      if room.contains p then
        match prev with
        | some q => if rooms.any (·.contains q) then none else some q
        | none => none
      else go rest (some p)
  go path none

structure Proposal where
  dungeon : Dungeon
  player : Pos
  monsters : List Monster
  deriving Repr, Inhabited

def colors : List Color := [.red, .green, .blue]

def shuffle (xs : List α) [Inhabited α] : Rand (List α) := do
  let mut rest := xs
  let mut out := []
  while !rest.isEmpty do
    let i ← rnd 0 (rest.length - 1)
    out := out ++ [rest[i]!]
    rest := rest.eraseIdx i
  return out

/-- One roll. `none` when room placement came out too sparse. -/
def propose : Rand (Option Proposal) := do
  let rooms ← placeRooms
  let n := rooms.length
  if n < 3 then return none
  let mut cells : Array Cell := Array.replicate (width * height) .wall
  for r in rooms do
    for p in r.cells do
      cells := carve cells p .floor
  -- corridors, room i-1 to room i
  let mut paths : List (List Pos) := []
  for i in [1:n] do
    let path := corridor rooms[i-1]!.center rooms[i]!.center (← coin)
    paths := paths ++ [path]
    for p in path do
      if cells[index p]! = .wall then cells := carve cells p .floor
  -- doors on up to three connections, keys in earlier rooms
  let doorCount := min 3 (n - 1)
  let targets := (← shuffle (List.range' 1 (n - 1))).take doorCount
  let palette ← shuffle colors
  let mut taken : List Pos := [rooms[0]!.center]
  let mut ci := 0
  for i in targets do
    let color := palette[ci]!
    ci := ci + 1
    match doorSpot paths[i-1]! rooms[i]! rooms with
    | none => pure ()
    | some spot =>
      let j ← rnd 0 (i - 1)
      let free := rooms[j]!.cells.filter fun p => cells[index p]! = .floor ∧ p ∉ taken
      if free.isEmpty then pure () else
        let kp ← pick free
        cells := carve cells spot (.door color)
        cells := carve cells kp (.key color)
        taken := kp :: taken
  -- stairs in the last room
  let last := rooms[n-1]!
  let free := last.cells.filter fun p => cells[index p]! = .floor ∧ p ∉ taken
  if free.isEmpty then return none
  let sp ← pick free
  cells := carve cells sp .stairs
  taken := sp :: taken
  -- monsters in rooms other than the first
  let mut monsters : List Monster := []
  for _ in [:monsterCount] do
    let j ← rnd 1 (n - 1)
    let free := rooms[j]!.cells.filter fun p => cells[index p]! = .floor ∧ p ∉ taken
    if free.isEmpty then continue
    let mp ← pick free
    monsters := monsters ++ [⟨mp, monsterHp⟩]
    taken := mp :: taken
  return some { dungeon := ⟨width, height, cells⟩, player := rooms[0]!.center, monsters }

/-- Rows of glyphs to a dungeon. `#` wall, `.` floor, `>` stairs, `R`/`G`/`B`
doors, `r`/`g`/`b` keys. -/
def ofRows (rows : List String) : Dungeon :=
  let cellOf : Char → Cell
    | '.' => .floor
    | '>' => .stairs
    | 'R' => .door .red | 'G' => .door .green | 'B' => .door .blue
    | 'r' => .key .red | 'g' => .key .green | 'b' => .key .blue
    | _ => .wall
  ⟨width, height, (rows.flatMap fun row => row.toList.map cellOf).toArray⟩

/-- The dungeon used when every roll was rejected. A small room, a locked door,
its key, and the stairs. -/
def fallbackDungeon : Dungeon := ofRows (
  [ "############################################################"
  , "#......#...................................................#"
  , "#......R...........>.......................................#"
  , "#..r...#...................................................#"
  , "############################################################" ]
  ++ List.replicate (height - 5) (String.ofList (List.replicate width '#')))

def fallbackPlayer : Pos := ⟨1, 1⟩

/-- Checked at compile time by `decide`: the fallback is Completable. -/
def fallback : Game :=
  ⟨{ dungeon := fallbackDungeon, player := fallbackPlayer, held := [], hp := playerHp,
      monsters := [] },
    ⟨by decide +kernel, check_sound (by decide +kernel)⟩⟩

/-- What a generation attempt produced. -/
structure Outcome where
  game : Game
  usedFallback : Bool
  attempts : Nat

/-- Roll until the checker accepts or the budget runs out. -/
def generate (seed : Nat) : Outcome := Id.run do
  let mut g := mkStdGen seed
  for i in [:budget] do
    let (p?, g') := propose.run g
    g := g'
    if let some p := p? then
      if let some game := Game.start? p.dungeon p.player playerHp p.monsters then
        return { game, usedFallback := false, attempts := i + 1 }
  return { game := fallback, usedFallback := true, attempts := budget }

end Crawl.Gen
