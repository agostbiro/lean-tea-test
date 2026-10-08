import Dungeon.Core
import Dungeon.Gen
import LeanTea.Tui.App

/-! # Terminal front end on lean-tea's widget runtime.

Pure model/update/view. The only thing this module knows about the proofs is
that `Game` carries them, so it never has to re-check anything. -/

namespace Crawl.Tui

open LeanTea.Tui (Box Style Key Widget App)

/-- A screen cell, as opposed to a dungeon `Cell`. -/
abbrev TCell := LeanTea.Tui.Cell

inductive Phase where
  | playing
  | won
  | dead
  deriving Repr, DecidableEq, Inhabited

structure Model where
  game : Game
  phase : Phase
  seed : Nat
  usedFallback : Bool
  attempts : Nat
  message : String
  quit : Bool := false

inductive Msg where
  | move (m : Move)
  | newGame
  | quit
  deriving Repr, DecidableEq, Inhabited

def describe : Event → String
  | .waited => "You wait."
  | .moved => ""
  | .blocked => "Something solid is in the way."
  | .lockedDoor c => s!"The {repr c} door is locked."
  | .openedDoor c => s!"You unlock the {repr c} door."
  | .pickedKey c => s!"You pick up the {repr c} key."
  | .reachedStairs => "You reach the stairs. You escaped!"
  | .hitMonster n => s!"You hit the monster ({n} hp left). It hits back."
  | .killedMonster => "You slay the monster."

def start (seed : Nat) : Model :=
  let o := Gen.generate seed
  { game := o.game, phase := .playing, seed := seed, usedFallback := o.usedFallback,
    attempts := o.attempts,
    message := if o.usedFallback then "Generation gave up; using the fallback dungeon."
               else "Find the stairs. Keys open doors of their color." }

def update (msg : Msg) (m : Model) : Model :=
  match msg with
  | .quit => { m with quit := true }
  | .newGame => start (m.seed + 1)
  | .move mv =>
    if m.phase ≠ .playing then m else
    let (g, ev) := m.game.step mv
    let phase := if g.won then .won else if g.dead then .dead else .playing
    let message := if g.dead then "You die. Press Enter for a new dungeon." else describe ev
    { m with game := g, phase := phase, message := message }

def colorStyle : Color → Style
  | .red => { fg := .bright .red, bold := true }
  | .green => { fg := .bright .green, bold := true }
  | .blue => { fg := .bright .blue, bold := true }

def colorLetter : Color → Char
  | .red => 'r'
  | .green => 'g'
  | .blue => 'b'

def glyph (s : State) (p : Pos) : TCell :=
  if p = s.player then { ch := '@', style := { fg := .bright .white, bold := true } }
  else match s.monsterAt p with
  | some _ => { ch := 'M', style := { fg := .bright .magenta, bold := true } }
  | none =>
    match s.dungeon.cellAt p with
    | .wall => { ch := '#', style := { fg := .white, dim := true } }
    | .floor => { ch := '.', style := { fg := .white, dim := true } }
    | .stairs => { ch := '>', style := { fg := .bright .yellow, bold := true } }
    | .door c =>
      if c ∈ s.held then { ch := '\'', style := colorStyle c }
      else { ch := '+', style := colorStyle c }
    | .key c =>
      if c ∈ s.held then { ch := '.', style := { fg := .white, dim := true } }
      else { ch := 'k', style := colorStyle c }

def statusLine (m : Model) : Array TCell := Id.run do
  let s := m.game.state
  let put := fun (row : Array TCell) (str : String) (st : Style) =>
    str.toList.foldl (fun r c => r.push { ch := c, style := st }) row
  let mut row := put #[] s!"HP {s.hp}/{Gen.playerHp}  keys: " {}
  for c in [Color.red, .green, .blue] do
    if c ∈ s.held then
      row := put row (String.singleton (colorLetter c)) (colorStyle c)
    else
      row := put row "-" { dim := true }
  row := put row s!"  seed {m.seed}  rolls {m.attempts}" {}
  if m.usedFallback then
    row := put row "  FALLBACK" { fg := .bright .yellow, bold := true }
  if m.phase = .won then
    row := put row "  ESCAPED" { fg := .bright .green, bold := true }
  if m.phase = .dead then
    row := put row "  DEAD" { fg := .bright .red, bold := true }
  return row

def helpLine : String :=
  "arrows/hjkl move  . wait  Enter new dungeon  q quit"

/-- Pad or cut a row to exactly `w` cells; the runtime indexes every column. -/
def fit (w : Nat) (row : Array TCell) : Array TCell :=
  if row.size ≥ w then row.extract 0 w else row ++ Array.replicate (w - row.size) ({} : TCell)

def render (m : Model) (w h : Nat) : Box := Id.run do
  let s := m.game.state
  let mut rows : Array (Array TCell) := #[]
  for y in [:s.dungeon.height] do
    let mut row : Array TCell := #[]
    for x in [:s.dungeon.width] do
      row := row.push (glyph s ⟨x, y⟩)
    rows := rows.push (fit w row)
  rows := rows.push (fit w (statusLine m))
  rows := rows.push (Box.textRow w m.message {})
  rows := rows.push (Box.textRow w helpLine { dim := true })
  while rows.size < h do rows := rows.push (Array.replicate w ({} : TCell))
  return { width := w, height := rows.size, cells := rows.extract 0 h }

def onKey : Key → Option Msg
  | .up | .char 'k' => some (.move (.step .up))
  | .down | .char 'j' => some (.move (.step .down))
  | .left | .char 'h' => some (.move (.step .left))
  | .right | .char 'l' => some (.move (.step .right))
  | .char '.' => some (.move .wait)
  | .enter | .char 'n' => some .newGame
  | .char 'q' | .esc => some .quit
  | _ => none

def view (m : Model) : Widget Msg :=
  { render := fun w h _ => render m w h, onKey := onKey, focusId := "game" }

def app (seed : Nat) : App Model Msg :=
  { init := start seed, view := view, update := update, quitWhen := (·.quit),
    initialFocus := "game" }

/-! ## Terminal runner

lean-tea's `App.runWith` ends each row with a bare `\n`. Under `stty raw`
output processing is off, so `\n` does not return to column 0 and the
screen comes out as a staircase. It also uses a fixed size. This runner
places every row with an absolute cursor move and asks the terminal for
its real size on every frame. -/

def ansi (s : String) : String := s!"\x1b[{s}"

def colorCode (c : LeanTea.Tui.Color) (bg : Bool) : String :=
  let code : LeanTea.Tui.Color → Option Nat
    | .black => some 0 | .red => some 1 | .green => some 2 | .yellow => some 3
    | .blue => some 4 | .magenta => some 5 | .cyan => some 6 | .white => some 7
    | _ => none
  let base := if bg then 40 else 30
  match c with
  | .bright cc => match code cc with
    | some n => ansi s!"{base + 60 + n}m"
    | none => ansi s!"{base + 9}m"
  | cc => ansi s!"{base + (code cc).getD 9}m"

def styleCode (s : Style) : String :=
  ansi "0m" ++ colorCode s.fg false ++ colorCode s.bg true
    ++ (if s.bold then ansi "1m" else "")
    ++ (if s.dim then ansi "2m" else "")
    ++ (if s.inverse then ansi "7m" else "")

/-- One full frame. Rows are placed with `CSI row;1H`, never `\n`. -/
def paint (box : Box) : String := Id.run do
  let mut out := ""
  for r in [:box.height] do
    out := out ++ ansi s!"{r + 1};1H" ++ ansi "0m"
    let mut cur : Option Style := none
    for cell in box.cells[r]! do
      if cur != some cell.style then
        out := out ++ styleCode cell.style
        cur := some cell.style
      out := out.push cell.ch
  return out ++ ansi "0m"

def sh (cmd : String) : IO String :=
  IO.Process.run { cmd := "sh", args := #["-c", cmd] }

/-- `(cols, rows)` of the controlling terminal, or 80x24 if unknown. -/
def termSize : IO (Nat × Nat) := do
  try
    match (← sh "stty size < /dev/tty").trimAscii.toString.splitOn " " with
    | [r, c] => match r.toNat?, c.toNat? with
      | some r, some c => if r > 0 && c > 0 then return (c, r) else return (80, 24)
      | _, _ => return (80, 24)
    | _ => return (80, 24)
  catch _ => return (80, 24)

partial def run (seed : Nat) : IO Unit := do
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin
  let saved ← try (·.trimAscii.toString) <$> sh "stty -g < /dev/tty" catch _ => pure ""
  let _ ← try sh "stty raw -echo < /dev/tty" catch _ => pure ""
  stdout.putStr (ansi "?1049h" ++ ansi "?25l" ++ ansi "2J")
  stdout.flush
  let a := app seed
  try
    let mut state := a.init
    let mut lastSize := (0, 0)
    while !(a.quitWhen state) do
      let (w, h) ← termSize
      -- After a resize, wipe leftovers from the old, larger frame.
      if (w, h) != lastSize then stdout.putStr (ansi "2J")
      lastSize := (w, h)
      let widget := a.view state
      stdout.putStr (paint (widget.render w h true))
      stdout.flush
      match ← LeanTea.Tui.readKey stdin with
      | .ctrl 'c' => break
      | key =>
        if let some msg := widget.dispatchKey "game" key then
          state := a.update msg state
  finally
    let restore := if saved.isEmpty then "-raw echo" else saved
    let _ ← try sh s!"stty {restore} < /dev/tty" catch _ => pure ""
    stdout.putStr (ansi "0m" ++ ansi "?25h" ++ ansi "?1049l")
    stdout.flush

end Crawl.Tui
