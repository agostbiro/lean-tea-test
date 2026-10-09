import Dungeon.Core.Reach

/-! # The checker and its soundness proof.

`check d k` searches over configs: which key cells are emptied and which doors
are open. For each config it finds the cells the player can walk to with a
breadth-first search, then branches on every key it could pick up and every
door it could unlock next. Configs with the same keys and doors are explored
once. Both searches are fuel-bounded so they are total; soundness does not
depend on the fuel. Only soundness is proved: if the checker says yes, the
dungeon is Completable. That is the direction the game relies on. -/

namespace Crawl
namespace Check

/-- One breadth-first search with fixed keys and doors. `visited` and
`frontier` are both lists of cells already known reachable. -/
def bfs (d : Dungeon) (k : Config) : Nat → List Pos → List Pos → List Pos
  | 0, visited, _ => visited
  | _ + 1, visited, [] => visited
  | fuel + 1, visited, p :: rest =>
    let fresh := p.neighbors.filter fun q => q ∉ visited ∧ q ∉ rest ∧ k.free d q = true
    bfs d k fuel (fresh ++ visited) (rest ++ fresh)

/-- The cells the player can walk to from `k` without changing anything. -/
def region (d : Dungeon) (k : Config) : List Pos :=
  bfs d k (d.width * d.height + 1) [k.pos] [k.pos]

/-- The config after entering `q`, if that picks up a key or unlocks a door. -/
def next (d : Dungeon) (k : Config) (q : Pos) : Option Config :=
  match d.cellAt q with
  | .key _ => if q ∈ k.got then none else some ⟨q, q :: k.got, k.opened⟩
  | .door c => if q ∉ k.opened ∧ 0 < k.held d c then some ⟨q, k.got, q :: k.opened⟩ else none
  | _ => none

/-- Every config one pickup or unlock away from the walkable cells `reg`. -/
def successors (d : Dungeon) (k : Config) (reg : List Pos) : List Config :=
  reg.flatMap fun p => p.neighbors.filterMap (next d k)

/-- Same emptied keys and opened doors, in any order. Position is ignored: every
config can walk back to the start, so its walkable cells only depend on these. -/
def sameSets (a b : Config) : Bool :=
  a.got.all (· ∈ b.got) && b.got.all (· ∈ a.got) &&
    a.opened.all (· ∈ b.opened) && b.opened.all (· ∈ a.opened)

/-- Queue the configs in `ns` not yet seen. -/
def enqueue (seen todo : List Config) : List Config → List Config × List Config
  | [] => (seen, todo)
  | n :: ns =>
    if seen.any (sameSets n) then enqueue seen todo ns
    else enqueue (n :: seen) (todo ++ [n]) ns

/-- Explore configs until one can walk to the Stairs. -/
def search (d : Dungeon) : Nat → List Config → List Config → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => false
  | fuel + 1, seen, k :: rest =>
    let reg := region d k
    if reg.any (fun p => d.cellAt p = .stairs) then true
    else
      let (seen', todo) := enqueue seen rest (successors d k reg)
      search d fuel seen' todo

/-- Configs to explore before giving up. -/
def searchFuel : Nat := 1024

end Check

/-- Does the checker find the Stairs? -/
def check (d : Dungeon) (k : Config) : Bool :=
  Check.search d Check.searchFuel [k] [k]

namespace Check

variable {d : Dungeon} {k₀ : Config}

theorem bfs_sound {k : Config} (hk : ∀ p, Steps d k₀ ⟨p, k.got, k.opened⟩ →
      ∀ q, Adj p q → k.free d q = true → Steps d k₀ ⟨q, k.got, k.opened⟩) :
    ∀ (fuel : Nat) (visited frontier : List Pos),
      (∀ p ∈ visited, Steps d k₀ ⟨p, k.got, k.opened⟩) →
      (∀ p ∈ frontier, Steps d k₀ ⟨p, k.got, k.opened⟩) →
      ∀ p ∈ bfs d k fuel visited frontier, Steps d k₀ ⟨p, k.got, k.opened⟩ := by
  intro fuel
  induction fuel with
  | zero => intro visited frontier hv _; simpa [bfs] using hv
  | succ fuel ih =>
    intro visited frontier hv hf
    cases frontier with
    | nil => simpa [bfs] using hv
    | cons p rest =>
      simp only [bfs]
      have hp := hf p (List.mem_cons_self ..)
      have hfresh : ∀ q ∈ p.neighbors.filter
          (fun q => q ∉ visited ∧ q ∉ rest ∧ k.free d q = true),
          Steps d k₀ ⟨q, k.got, k.opened⟩ := by
        intro q hq
        rw [List.mem_filter] at hq
        obtain ⟨hn, hcond⟩ := hq
        simp only [decide_eq_true_eq] at hcond
        exact hk p hp q (Pos.mem_neighbors_adj hn) hcond.2.2
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

/-- Every cell of the region is reachable, with the same keys and doors. -/
theorem region_sound {k : Config} (h : Steps d k₀ k) :
    ∀ p ∈ region d k, Steps d k₀ ⟨p, k.got, k.opened⟩ := by
  have hk : Steps d k₀ ⟨k.pos, k.got, k.opened⟩ := h
  refine bfs_sound ?_ _ _ _ (by simpa using hk) (by simpa using hk)
  intro p hp q hadj hq
  exact hp.tail (Step.walk (k := ⟨p, k.got, k.opened⟩) hadj hq)

theorem next_sound {k k' : Config} {p q : Pos} (hadj : Adj p q) (h : next d k q = some k') :
    Step d ⟨p, k.got, k.opened⟩ k' := by
  unfold next at h
  split at h
  · rename_i c hc
    split at h
    · cases h
    · rename_i hn
      cases h
      exact Step.pick (k := ⟨p, k.got, k.opened⟩) hadj hc hn
  · rename_i c hc
    split at h
    · rename_i hcond
      cases h
      exact Step.unlock (k := ⟨p, k.got, k.opened⟩) hadj hc hcond.1 hcond.2
    · cases h
  · cases h

theorem successors_sound {k : Config} {reg : List Pos}
    (hreg : ∀ p ∈ reg, Steps d k₀ ⟨p, k.got, k.opened⟩) :
    ∀ n ∈ successors d k reg, Steps d k₀ n := by
  intro n hn
  simp only [successors, List.mem_flatMap, List.mem_filterMap] at hn
  obtain ⟨p, hp, q, hq, hnext⟩ := hn
  exact (hreg p hp).tail (next_sound (Pos.mem_neighbors_adj hq) hnext)

theorem enqueue_sound : ∀ (ns seen todo : List Config),
    (∀ n ∈ todo, Steps d k₀ n) → (∀ n ∈ ns, Steps d k₀ n) →
    ∀ n ∈ (enqueue seen todo ns).2, Steps d k₀ n := by
  intro ns
  induction ns with
  | nil => intro _ _ ht _; simpa [enqueue] using ht
  | cons m ms ih =>
    intro seen todo ht hns
    have hms : ∀ n ∈ ms, Steps d k₀ n := fun n hn => hns n (List.mem_cons_of_mem _ hn)
    simp only [enqueue]
    split
    · exact ih _ _ ht hms
    · refine ih _ _ ?_ hms
      intro n hn
      rw [List.mem_append, List.mem_singleton] at hn
      rcases hn with hn | rfl
      · exact ht n hn
      · exact hns n (List.mem_cons_self ..)

theorem search_sound : ∀ (fuel : Nat) (seen todo : List Config),
    (∀ n ∈ todo, Steps d k₀ n) → search d fuel seen todo = true → Completable d k₀ := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [search] at h
  | succ fuel ih =>
    intro seen todo ht h
    cases todo with
    | nil => simp [search] at h
    | cons k rest =>
      have hk := ht k (List.mem_cons_self ..)
      have hreg := region_sound hk
      simp only [search] at h
      split at h
      · rename_i hany
        rw [List.any_eq_true] at hany
        obtain ⟨p, hp, hs⟩ := hany
        simp only [decide_eq_true_eq] at hs
        exact ⟨_, hreg p hp, hs⟩
      · have hrest : ∀ n ∈ rest, Steps d k₀ n := fun n hn => ht n (List.mem_cons_of_mem _ hn)
        exact ih _ _ (enqueue_sound _ _ _ hrest (successors_sound hreg)) h

end Check

/-- **Checker soundness.** If the checker accepts, the dungeon is Completable. -/
theorem check_sound {d : Dungeon} {k : Config} (h : check d k = true) : Completable d k :=
  Check.search_sound _ _ _ (by simp [Relation.ReflTransGen.refl]) h

end Crawl
