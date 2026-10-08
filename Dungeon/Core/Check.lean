import Dungeon.Core.Reach

/-! # The checker and its soundness proof.

`check d start held` is a breadth-first search over the grid, repeated until no
new key color turns up. It is fuel-bounded so it is total; soundness does not
depend on the fuel. Only soundness is proved: if the checker says yes, the
dungeon is Completable. That is the direction the game relies on. -/

namespace Crawl
namespace Check

/-- Colors of keys lying on the given cells. -/
def keysOn (d : Dungeon) (cells : List Pos) : List Color :=
  cells.filterMap fun p =>
    match d.cellAt p with
    | .key c => some c
    | _ => none

/-- One breadth-first search with a fixed key set. `visited` and `frontier`
are both lists of cells already known reachable. -/
def bfs (d : Dungeon) (known : Held) : Nat → List Pos → List Pos → List Pos
  | 0, visited, _ => visited
  | _ + 1, visited, [] => visited
  | fuel + 1, visited, p :: rest =>
    let fresh := p.neighbors.filter fun q =>
      q ∉ visited ∧ q ∉ rest ∧ (d.cellAt q).passable known
    bfs d known fuel (fresh ++ visited) (rest ++ fresh)

/-- Repeat the search until the set of known key colors stops growing. -/
def rounds (d : Dungeon) (start : Pos) (held : Held) : Nat → Held → List Pos
  | 0, known => bfs d known (d.width * d.height + 1) [start] [start]
  | n + 1, known =>
    let visited := bfs d known (d.width * d.height + 1) [start] [start]
    let known' := keysOn d visited ++ held
    if known' ⊆ known then visited else rounds d start held n known'

end Check

/-- All cells the checker finds reachable. -/
def reachableCells (d : Dungeon) (start : Pos) (held : Held) : List Pos :=
  Check.rounds d start held 4 held

/-- Does the checker find the Stairs? -/
def check (d : Dungeon) (start : Pos) (held : Held) : Bool :=
  (reachableCells d start held).any fun p => d.cellAt p = .stairs

namespace Check

/-- What the search assumes about its key set: each color is held or lies on a
reachable cell. -/
def KnownOk (d : Dungeon) (start : Pos) (held : Held) (known : Held) : Prop :=
  ∀ c ∈ known, c ∈ held ∨ ∃ r, Reachable d start held r ∧ d.cellAt r = .key c

theorem step_known {d start held known} (hk : KnownOk d start held known) {p q : Pos}
    (hp : Reachable d start held p) (hadj : Adj p q) (hq : (d.cellAt q).passable known) :
    Reachable d start held q := by
  rcases hq with hq | ⟨c, hc, hm⟩
  · exact Reachable.step hp hadj hq
  · rcases hk c hm with h | ⟨r, hr, hkr⟩
    · exact Reachable.heldDoor hp hadj hc h
    · exact Reachable.foundDoor hp hadj hc hr hkr

theorem bfs_sound {d start held known} (hk : KnownOk d start held known) :
    ∀ (fuel : Nat) (visited frontier : List Pos),
      (∀ p ∈ visited, Reachable d start held p) →
      (∀ p ∈ frontier, Reachable d start held p) →
      ∀ p ∈ bfs d known fuel visited frontier, Reachable d start held p := by
  intro fuel
  induction fuel with
  | zero => intro visited frontier hv _; simpa [bfs] using hv
  | succ fuel ih =>
    intro visited frontier hv hf
    cases frontier with
    | nil => simpa [bfs] using hv
    | cons p rest =>
      simp only [bfs]
      have hp : Reachable d start held p := hf p (List.mem_cons_self ..)
      have hfresh : ∀ q ∈ p.neighbors.filter
          (fun q => q ∉ visited ∧ q ∉ rest ∧ (d.cellAt q).passable known),
          Reachable d start held q := by
        intro q hq
        rw [List.mem_filter] at hq
        obtain ⟨hn, hcond⟩ := hq
        simp only [decide_eq_true_eq] at hcond
        exact step_known hk hp (Pos.mem_neighbors_adj hn) hcond.2.2
      apply ih
      · intro q hq
        rw [List.mem_append] at hq
        rcases hq with hq | hq
        · exact hfresh q hq
        · exact hv q hq
      · intro q hq
        rw [List.mem_append] at hq
        rcases hq with hq | hq
        · exact hf q (List.mem_cons_of_mem _ hq)
        · exact hfresh q hq

theorem keysOn_known {d start held} {cells : List Pos}
    (hc : ∀ p ∈ cells, Reachable d start held p) :
    KnownOk d start held (keysOn d cells ++ held) := by
  intro c hc'
  rw [List.mem_append] at hc'
  rcases hc' with h | h
  · right
    unfold keysOn at h
    rw [List.mem_filterMap] at h
    obtain ⟨r, hr, hmatch⟩ := h
    refine ⟨r, hc r hr, ?_⟩
    revert hmatch
    cases d.cellAt r <;> simp
  · exact Or.inl h

theorem rounds_sound {d start held} : ∀ (n : Nat) (known : Held),
    KnownOk d start held known →
    ∀ p ∈ rounds d start held n known, Reachable d start held p := by
  intro n
  induction n with
  | zero =>
    intro known hk p hp
    simp only [rounds] at hp
    exact bfs_sound hk _ _ _ (by simp [Reachable.start]) (by simp [Reachable.start]) p hp
  | succ n ih =>
    intro known hk p hp
    simp only [rounds] at hp
    have hvis := bfs_sound hk (d.width * d.height + 1) [start] [start]
      (by simp [Reachable.start]) (by simp [Reachable.start])
    split at hp
    · exact hvis p hp
    · exact ih _ (keysOn_known hvis) p hp

theorem held_known {d start held} : KnownOk d start held held :=
  fun _ hc => Or.inl hc

end Check

/-- Every cell the checker reports is reachable. -/
theorem reachableCells_sound {d start held} :
    ∀ p ∈ reachableCells d start held, Reachable d start held p :=
  Check.rounds_sound 4 held Check.held_known

/-- **Checker soundness.** If the checker accepts, the dungeon is Completable. -/
theorem check_sound {d start held} (h : check d start held = true) :
    Completable d start held := by
  unfold check at h
  rw [List.any_eq_true] at h
  obtain ⟨p, hp, hs⟩ := h
  simp only [decide_eq_true_eq] at hs
  exact ⟨p, hs, reachableCells_sound p hp⟩

end Crawl
