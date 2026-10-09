import Dungeon.Core.Basic

/-! # Moves on the grid and the meaning of Completable.

The dungeon grid never changes. What the player has done to it is a `Config`:
where they stand, which key cells they have emptied and which doors they have
opened. `Step` is one move in this model, with keys spent on doors, and
`Completable` says some sequence of steps reaches the Stairs. This is the
semantic definition the headline theorem is about; the checker in
`Dungeon.Core.Check` is proved sound against it. -/

namespace Crawl

/-- The player's position plus the parts of the dungeon they have changed:
key cells they have emptied and doors they have opened. -/
structure Config where
  pos : Pos
  got : List Pos
  opened : List Pos
  deriving DecidableEq, Repr, Inhabited

/-- Keys of a color in hand: those picked up minus those spent on doors. -/
def Config.held (k : Config) (d : Dungeon) (c : Color) : Nat :=
  k.got.countP (fun p => d.cellAt p = .key c) - k.opened.countP (fun p => d.cellAt p = .door c)

/-- A cell the player can walk onto without changing anything: floor, stairs,
an emptied key cell or an opened door. -/
def Config.free (k : Config) (d : Dungeon) (q : Pos) : Bool :=
  match d.cellAt q with
  | .floor | .stairs => true
  | .key _ => q ∈ k.got
  | .door _ => q ∈ k.opened
  | .wall => false

/-- One move. Walking changes nothing but the position. Picking up a key empties
its cell. Unlocking a door spends a key and leaves the door open for good. -/
inductive Step (d : Dungeon) : Config → Config → Prop
  | walk {k : Config} {q : Pos} (hadj : Adj k.pos q) (hq : k.free d q = true) :
      Step d k ⟨q, k.got, k.opened⟩
  | pick {k : Config} {q : Pos} {c : Color} (hadj : Adj k.pos q) (hq : d.cellAt q = .key c)
      (hn : q ∉ k.got) : Step d k ⟨q, q :: k.got, k.opened⟩
  | unlock {k : Config} {q : Pos} {c : Color} (hadj : Adj k.pos q) (hq : d.cellAt q = .door c)
      (hn : q ∉ k.opened) (hk : 0 < k.held d c) : Step d k ⟨q, k.got, q :: k.opened⟩

abbrev Steps (d : Dungeon) : Config → Config → Prop := Relation.ReflTransGen (Step d)

/-- Some sequence of moves reaches the Stairs. -/
def Completable (d : Dungeon) (k : Config) : Prop :=
  ∃ k', Steps d k k' ∧ d.cellAt k'.pos = .stairs

/-- The cell the player stands on can be walked back onto. This is what lets a
move be undone, which is the heart of move preservation. -/
def StandOk (d : Dungeon) (k : Config) : Prop :=
  k.free d k.pos = true

instance (d : Dungeon) (k : Config) : Decidable (StandOk d k) :=
  inferInstanceAs (Decidable (k.free d k.pos = true))

/-- Stepping next to the player keeps the Stairs reachable: walk back first. -/
theorem Completable.back {d : Dungeon} {k : Config} {q : Pos} (hadj : Adj q k.pos)
    (hs : StandOk d k) (h : Completable d k) : Completable d ⟨q, k.got, k.opened⟩ := by
  obtain ⟨k', hk', hst⟩ := h
  refine ⟨k', Relation.ReflTransGen.head ?_ hk', hst⟩
  exact Step.walk (k := ⟨q, k.got, k.opened⟩) hadj hs

/-- `b` is `a` with possibly some keys already picked up. Every move from `a`
can be copied from `b`, so `b` is at least as well off. -/
structure Ahead (a b : Config) : Prop where
  pos : a.pos = b.pos
  opened : a.opened = b.opened
  got : a.got ⊆ b.got
  nodup : a.got.Nodup

namespace Ahead

theorem held_le {d : Dungeon} {a b : Config} (h : Ahead a b) (c : Color) :
    a.held d c ≤ b.held d c := by
  unfold Config.held
  rw [h.opened]
  exact Nat.sub_le_sub_right ((h.nodup.subperm h.got).countP_le _) _

theorem free {d : Dungeon} {a b : Config} (h : Ahead a b) {q : Pos}
    (hq : a.free d q = true) : b.free d q = true := by
  unfold Config.free at *
  generalize d.cellAt q = cell at hq ⊢
  cases cell <;> simp only [decide_eq_true_eq] at hq ⊢
  case key => exact h.got hq
  case door => exact h.opened ▸ hq
  case wall => exact hq

theorem step {d : Dungeon} {a a' b : Config} (h : Ahead a b) (hs : Step d a a') :
    ∃ b', Step d b b' ∧ Ahead a' b' := by
  cases hs with
  | walk hadj hq =>
    exact ⟨_, Step.walk (h.pos ▸ hadj) (h.free hq), ⟨rfl, h.opened, h.got, h.nodup⟩⟩
  | @pick q c hadj hq hn =>
    by_cases hb : q ∈ b.got
    · refine ⟨_, Step.walk (h.pos ▸ hadj) (by simp [Config.free, hq, hb]), ?_⟩
      exact ⟨rfl, h.opened, List.cons_subset.2 ⟨hb, h.got⟩, List.nodup_cons.2 ⟨hn, h.nodup⟩⟩
    · refine ⟨_, Step.pick (h.pos ▸ hadj) hq hb, ?_⟩
      exact ⟨rfl, h.opened, List.cons_subset_cons _ h.got, List.nodup_cons.2 ⟨hn, h.nodup⟩⟩
  | unlock hadj hq hn hk =>
    refine ⟨_, Step.unlock (h.pos ▸ hadj) hq (h.opened ▸ hn) (Nat.lt_of_lt_of_le hk (h.held_le _)),
      ⟨rfl, by simp [h.opened], h.got, h.nodup⟩⟩

theorem steps {d : Dungeon} {a a' b : Config} (h : Ahead a b) (hs : Steps d a a') :
    ∃ b', Steps d b b' ∧ Ahead a' b' := by
  induction hs with
  | refl => exact ⟨b, Relation.ReflTransGen.refl, h⟩
  | tail _ hs ih =>
    obtain ⟨b', hb', hab'⟩ := ih
    obtain ⟨b'', hb'', hab''⟩ := hab'.step hs
    exact ⟨b'', hb'.tail hb'', hab''⟩

end Ahead

/-- Holding keys early never hurts. -/
theorem Completable.ahead {d : Dungeon} {a b : Config} (h : Ahead a b) (hc : Completable d a) :
    Completable d b := by
  obtain ⟨a', ha', hst⟩ := hc
  obtain ⟨b', hb', hab⟩ := h.steps ha'
  exact ⟨b', hb', hab.pos ▸ hst⟩

end Crawl
