# Follow-ups

Deferred during the design session on 2026-10-08, in the order they were agreed.
Each entry says what changes in the proven core, because that is the cost that
matters here.

## 1. Consumable keys

A key is spent when a door opens. This is the agreed second milestone and the
one that makes the no-softlock theorem interesting, since a player could waste
a key on the wrong door.

- `Cell.pickUp` becomes a count per color, not a membership list. `Held` turns
  into something like `Color → Nat`.
- `State.step` removes a key when the player enters a door, and an opened door
  must become permanently open (a new cell state, or a set of opened doors in
  `State`), otherwise walking back through it would cost a second key.
- `Reachable.foundDoor` is no longer valid as stated: a key found on a reachable
  cell opens one door, not every door of its color. The semantic definition
  needs a resource-aware formulation, and `rebase_adj` needs the opened door to
  stay passable without a key.
- The checker becomes a search over (position, keys held, doors opened) rather
  than a fixed point on colors. Soundness proof shape stays the same.
- The generator must place keys so that no reachable wrong door can strand the
  player, or `State.step` must refuse a door-opening move that would make the
  state non-Completable. The second option keeps the generator unproven, which
  matches `docs/adr/0001`, but it means the rules consult the checker.
- `Tests.lean` walkthrough needs a case for "key spent, door stays open".

## 2. Chasing monsters

Monsters step toward the player when in line of sight, after each player move.

- Adds a monster turn to `State.step`. The theorem does not mention monsters,
  so `step_inv` only needs the monster phase to leave `dungeon`, `player` and
  `held` untouched, which the current `attack_inv` pattern already shows how
  to prove.
- The wait key becomes meaningful.
- Needs a small line-of-sight or distance check and a pathing step. Keep both
  in the unproven part.

## 3. Fog of war

Cells become visible once the player has been near them.

- Renderer-only. Add a seen-set to `Tui.Model`, not to `State`, so nothing in
  the proven core changes.
- Line of sight with walls blocking is a bigger step and can wait.

## 4. Descend

Reaching the stairs generates the next dungeon as a deeper floor, carrying hit
points over, with a depth counter.

- Reopens the `Dungeon` glossary entry in `CONTEXT.md`, which currently says
  one dungeon per game.
- `Tui.update` already regenerates in-process, so this is mostly a counter and
  a different `start`.

## 5. Explicit commands and inventory

Pick up, drop, open, and an inventory screen.

- Only worth doing together with consumable keys, where drop is the main
  softlock vector and must either be refused or proven safe.

## Smaller items

- The generator never uses the fallback across 200 seeds, so the fallback path
  in `Tui` has only been exercised by the scripted test, not visually.
- lean-tea is pinned to one commit in `lakefile.toml`; bumping it means
  re-checking the widget runtime's key dispatch, which only reaches the widget
  whose focus id is focused.
- Mathlib is lightly used. If build size becomes a problem, the core proofs
  can likely be rewritten against core Lean and Batteries; see
  `docs/adr/0003`.
- Decidability instances used by kernel `decide` must be written by hand, not
  by tactic. The `Cell.passable` instance has a note explaining why.
