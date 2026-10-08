import Dungeon
import Plausible

/-! # Checks that run with `lake build`.

The `#guard_msgs` blocks fail the build if the headline theorems ever pick up
an axiom beyond the standard three (so no `sorry`, no `native_decide`). The
executable sweeps seeds and fails if the generator ever falls back. -/

open Crawl

/-- info: 'Crawl.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_sound

/-- info: 'Crawl.State.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms State.step_inv

/-- info: 'Crawl.Game.step_completable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Game.step_completable

/-- info: 'Crawl.Gen.fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Gen.fallback

-- Plausible samples seeds; every roll must be accepted without the fallback.
#test ∀ seed : Nat, (Gen.generate seed).usedFallback = false

/-- Walk the fallback dungeon by hand: bump the locked door, fetch the key,
open the door, reach the stairs. Exercises every rule except combat. -/
def walkFallback : IO Bool := do
  let g := Gen.fallback
  let mut ok := true
  let expect := fun (name : String) (cond : Bool) => do
    if !cond then IO.eprintln s!"walkFallback: {name} failed"
    pure cond
  let play := fun (g : Game) (moves : List Move) =>
    moves.foldl (fun (acc : Game × Event) m => acc.1.step m) (g, .waited)
  -- east along row 1 to (6,1), down to (6,2), bump the red door at (7,2)
  let (g1, ev1) := play g (List.replicate 5 (Move.step .right) ++ [.step .down, .step .right])
  ok := ok && (← expect "locked door" (ev1 = .lockedDoor .red))
  ok := ok && (← expect "still at (6,2)" (g1.state.player = ⟨6, 2⟩))
  -- fetch the key at (3,3)
  let (g2, ev2) := play g1 (List.replicate 3 (Move.step .left) ++ [.step .down])
  ok := ok && (← expect "picked red key" (ev2 = .pickedKey .red))
  -- back to the door and through it
  let (g3, ev3) := play g2 ([Move.step .up] ++ List.replicate 4 (Move.step .right))
  ok := ok && (← expect "opened red door" (ev3 = .openedDoor .red))
  -- on to the stairs at (19,2)
  let (g4, ev4) := play g3 (List.replicate 12 (Move.step .right))
  ok := ok && (← expect "reached stairs" (ev4 = .reachedStairs))
  ok := ok && (← expect "won" g4.won)
  return ok

def main : IO UInt32 := do
  let walked ← walkFallback
  IO.println s!"fallback walkthrough: {if walked then "ok" else "FAILED"}"
  let n := 200
  let mut fallbacks := 0
  let mut rolls := 0
  let mut worst := 0
  for seed in [:n] do
    let o := Gen.generate seed
    rolls := rolls + o.attempts
    worst := max worst o.attempts
    if o.usedFallback then
      fallbacks := fallbacks + 1
      IO.eprintln s!"seed {seed}: fallback"
  IO.println s!"{n} seeds, {fallbacks} fallbacks, {rolls} rolls total, worst {worst}"
  return if fallbacks = 0 ∧ walked then 0 else 1
