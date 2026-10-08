import Mathlib.Tactic

/-! # Core vocabulary: colors, cells, positions, dungeons.

Everything in `Dungeon.Core` is total and proof-carrying. See `CONTEXT.md`
for the vocabulary. -/

namespace Crawl

/-- The label shared by a Door and the Keys that open it. -/
inductive Color where
  | red | green | blue
  deriving DecidableEq, Repr, Inhabited

/-- What a single cell of the grid holds. Keys and the Stairs are cells too. -/
inductive Cell where
  | wall
  | floor
  | door (c : Color)
  | key (c : Color)
  | stairs
  deriving DecidableEq, Repr, Inhabited

/-- A cell the player may always enter, whatever keys they hold. -/
def Cell.isOpen : Cell → Bool
  | .floor => true
  | .key _ => true
  | .stairs => true
  | _ => false

/-- A grid position. Row-major, `x` to the right, `y` down. -/
structure Pos where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The four directions a player can step. -/
inductive Dir where
  | up | down | left | right
  deriving DecidableEq, Repr, Inhabited

/-- Step one cell in a direction. `none` when that would leave the grid on the
left or top; the right and bottom edges are handled by `Dungeon.cellAt`, which
treats anything outside the grid as wall. -/
def Pos.move (p : Pos) : Dir → Option Pos
  | .up => if p.y = 0 then none else some ⟨p.x, p.y - 1⟩
  | .down => some ⟨p.x, p.y + 1⟩
  | .left => if p.x = 0 then none else some ⟨p.x - 1, p.y⟩
  | .right => some ⟨p.x + 1, p.y⟩

/-- Two positions share an edge. -/
def Adj (p q : Pos) : Prop :=
  (p.x = q.x ∧ (p.y + 1 = q.y ∨ q.y + 1 = p.y)) ∨
  (p.y = q.y ∧ (p.x + 1 = q.x ∨ q.x + 1 = p.x))

theorem Adj.symm {p q : Pos} (h : Adj p q) : Adj q p := by
  unfold Adj at *
  omega

theorem Pos.move_adj {p q : Pos} {d : Dir} (h : p.move d = some q) : Adj p q := by
  cases d
  · by_cases hy : p.y = 0
    · simp [Pos.move, hy] at h
    · simp only [Pos.move, hy, if_false, Option.some.injEq] at h
      subst h; simp only [Adj, true_and]; omega
  · simp only [Pos.move, Option.some.injEq] at h
    subst h; simp [Adj]
  · by_cases hx : p.x = 0
    · simp [Pos.move, hx] at h
    · simp only [Pos.move, hx, if_false, Option.some.injEq] at h
      subst h; simp only [Adj, true_and]; omega
  · simp only [Pos.move, Option.some.injEq] at h
    subst h; simp [Adj]

/-- The cells one step away in each direction. Used by the checker;
`mem_neighbors_adj` is what the soundness proof needs from it. -/
def Pos.neighbors (p : Pos) : List Pos :=
  [Dir.up, Dir.down, Dir.left, Dir.right].filterMap p.move

theorem Pos.mem_neighbors_adj {p q : Pos} (h : q ∈ p.neighbors) : Adj p q := by
  unfold Pos.neighbors at h
  rw [List.mem_filterMap] at h
  obtain ⟨d, _, hd⟩ := h
  exact Pos.move_adj hd

/-- A dungeon: a fixed-size grid of cells, row-major. -/
structure Dungeon where
  width : Nat
  height : Nat
  cells : Array Cell
  deriving Repr, Inhabited

/-- Cell lookup. Anything outside the grid, or beyond the array, is wall. -/
def Dungeon.cellAt (d : Dungeon) (p : Pos) : Cell :=
  if p.x < d.width ∧ p.y < d.height then d.cells.getD (p.y * d.width + p.x) .wall else .wall

/-- Keys currently held. A list because the proofs only ever ask about
membership and growth. -/
abbrev Held := List Color

/-- A cell is passable with the keys held: open cells always, doors only when
the matching color is held. -/
def Cell.passable (c : Cell) (held : Held) : Prop :=
  c.isOpen = true ∨ ∃ col, c = .door col ∧ col ∈ held

/-- Written by hand, not by tactic, so the kernel can evaluate it when the
fallback dungeon is checked by `decide`. -/
instance (c : Cell) (held : Held) : Decidable (c.passable held) :=
  match c with
  | .wall => isFalse (by simp [Cell.passable, Cell.isOpen])
  | .floor => isTrue (Or.inl rfl)
  | .key _ => isTrue (Or.inl rfl)
  | .stairs => isTrue (Or.inl rfl)
  | .door col =>
    if h : col ∈ held then isTrue (Or.inr ⟨col, rfl, h⟩)
    else isFalse (by simp [Cell.passable, Cell.isOpen, h])

theorem Cell.passable_mono {c : Cell} {h h' : Held} (sub : h ⊆ h') (hp : c.passable h) :
    c.passable h' := by
  rcases hp with hp | ⟨col, rfl, hm⟩
  · exact Or.inl hp
  · exact Or.inr ⟨col, rfl, sub hm⟩

/-- The keys held after stepping onto a cell. -/
def Cell.pickUp (c : Cell) (held : Held) : Held :=
  match c with
  | .key col => col :: held
  | _ => held

theorem Cell.subset_pickUp (c : Cell) (held : Held) : held ⊆ c.pickUp held := by
  cases c <;> simp [Cell.pickUp]

end Crawl
