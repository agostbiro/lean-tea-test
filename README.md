# Dungeon Crawl

A turn-based roguelike for the terminal, written in Lean 4 on
[lean-tea](https://github.com/Verilean/lean-tea), whose point is one theorem:
**the game can never be softlocked.** Every dungeon it shows you can be
finished, and nothing you do can change that.

## Build and run

```
lake build          # fetches Mathlib from the prebuilt cache on first run
./.lake/build/bin/dungeon          # random seed
./.lake/build/bin/dungeon 7        # fixed seed
./.lake/build/bin/DungeonTests     # seed sweep and a scripted walkthrough
```

Arrows or `hjkl` move, `.` waits, Enter starts a new dungeon, `q` quits.
Bump a monster to attack it. Keys open doors of their color and are never
spent.

## The theorem

`Dungeon/Core` is the proven part. It is total: no `partial`, no `sorry`, no
`native_decide`. `Tests.lean` fails the build if any of the headline results
picks up an axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

- `Reachable` (`Core/Reach.lean`) is the meaning of "the player can get
  there": open cells are passable, a door is passable if its color is held or a
  key of that color lies on a reachable cell. `Completable` means the stairs are
  reachable.
- `check_sound` (`Core/Check.lean`): if the checker accepts a dungeon, it is
  `Completable`. The generator is unproven and may propose anything; the game
  only accepts what the checker approves.
- `State.step_inv` (`Core/Rules.lean`): every legal move preserves
  `Completable`. The proof is that a move can be undone, so whatever was
  reachable before is reachable after, and picking up a key only helps.
- `Game` packages a state with its invariant, so `Game.completable` holds for
  every state the game can be in, by construction.

If generation gives up, a hand-written fallback dungeon is used; its proof is
`decide` run by the kernel at compile time, and the status line says so.

Vocabulary is in `CONTEXT.md`; design decisions in `docs/adr/`.
