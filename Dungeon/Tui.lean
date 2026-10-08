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

def run (seed : Nat) : IO Unit :=
  (app seed).runWith { width := 80, height := 24, focusOrder := ["game"] }

end Crawl.Tui
