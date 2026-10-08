import Dungeon.Core.Basic

/-! # Reachability and the meaning of Completable.

`Reachable d start held` is the set of cells the player can get to from
`start` holding `held`, where a door opens if its color is held or if a key of
its color lies on some reachable cell. Keys are never spent. This is the
semantic definition the headline theorem is about; the checker in
`Dungeon.Core.Check` is proved sound against it. -/

namespace Crawl

inductive Reachable (d : Dungeon) (start : Pos) (held : Held) : Pos → Prop
  | start : Reachable d start held start
  | step {p q : Pos} (hp : Reachable d start held p) (hadj : Adj p q)
      (hq : (d.cellAt q).isOpen = true) : Reachable d start held q
  | heldDoor {p q : Pos} {c : Color} (hp : Reachable d start held p) (hadj : Adj p q)
      (hq : d.cellAt q = .door c) (hc : c ∈ held) : Reachable d start held q
  | foundDoor {p q r : Pos} {c : Color} (hp : Reachable d start held p) (hadj : Adj p q)
      (hq : d.cellAt q = .door c) (hr : Reachable d start held r)
      (hk : d.cellAt r = .key c) : Reachable d start held q

/-- The Stairs are reachable. -/
def Completable (d : Dungeon) (start : Pos) (held : Held) : Prop :=
  ∃ s, d.cellAt s = .stairs ∧ Reachable d start held s

/-- The cell the player stands on can be entered with the keys held. This is
what lets a move be undone, which is the heart of move preservation. -/
def StandOk (d : Dungeon) (held : Held) (p : Pos) : Prop :=
  (d.cellAt p).passable held

instance (d : Dungeon) (held : Held) (p : Pos) : Decidable (StandOk d held p) :=
  inferInstanceAs (Decidable ((d.cellAt p).passable held))

namespace Reachable

/-- A passable neighbour of a reachable cell is reachable. -/
theorem step_passable {d start held} {p q : Pos} (hp : Reachable d start held p)
    (hadj : Adj p q) (hq : (d.cellAt q).passable held) : Reachable d start held q := by
  rcases hq with hq | ⟨c, hc, hm⟩
  · exact Reachable.step hp hadj hq
  · exact Reachable.heldDoor hp hadj hc hm

/-- Holding more keys never loses reachability. -/
theorem mono {d start} {held held' : Held} (sub : held ⊆ held') {p : Pos}
    (h : Reachable d start held p) : Reachable d start held' p := by
  induction h with
  | start => exact Reachable.start
  | step _ hadj hq ih => exact Reachable.step ih hadj hq
  | heldDoor _ hadj hq hc ih => exact Reachable.heldDoor ih hadj hq (sub hc)
  | foundDoor _ hadj hq _ hk ih ihr => exact Reachable.foundDoor ih hadj hq ihr hk

/-- Everything reachable from `s` is reachable from an adjacent `q`, provided
`s` itself can be re-entered. -/
theorem rebase_adj {d held} {s q : Pos} (hadj : Adj s q) (hs : StandOk d held s)
    {p : Pos} (h : Reachable d s held p) : Reachable d q held p := by
  induction h with
  | start => exact step_passable Reachable.start hadj.symm hs
  | step _ hadj' hq ih => exact Reachable.step ih hadj' hq
  | heldDoor _ hadj' hq hc ih => exact Reachable.heldDoor ih hadj' hq hc
  | foundDoor _ hadj' hq _ hk ih ihr => exact Reachable.foundDoor ih hadj' hq ihr hk

end Reachable

theorem Completable.mono {d start} {held held' : Held} (sub : held ⊆ held')
    (h : Completable d start held) : Completable d start held' :=
  let ⟨s, hs, hr⟩ := h
  ⟨s, hs, hr.mono sub⟩

theorem Completable.rebase_adj {d held} {s q : Pos} (hadj : Adj s q) (hs : StandOk d held s)
    (h : Completable d s held) : Completable d q held :=
  let ⟨t, ht, hr⟩ := h
  ⟨t, ht, hr.rebase_adj hadj hs⟩

theorem StandOk.mono {d} {held held' : Held} (sub : held ⊆ held') {p : Pos}
    (h : StandOk d held p) : StandOk d held' p :=
  Cell.passable_mono sub h

end Crawl
