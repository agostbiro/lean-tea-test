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
Bump a monster to attack it. A key opens one door of its color and is spent;
the door stays open. The game refuses to open a door if spending the key there
would leave the stairs out of reach.

## The theorem

`Dungeon/Core` is the proven part. It is total: no `partial`, no `sorry`, no
`native_decide`. `Tests.lean` fails the build if any of the headline results
picks up an axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

- `Step` (`Core/Reach.lean`) is one move in the model: walk onto a free cell,
  pick up a key, or spend a key to open a door for good. `Completable` means
  some sequence of steps reaches the stairs.
- `check_sound` (`Core/Check.lean`): if the checker accepts a dungeon, it is
  `Completable`. The generator is unproven and may propose anything; the game
  only accepts what the checker approves.
- `State.step_inv` (`Core/Rules.lean`): every legal move preserves
  `Completable`. A walk can be undone, so the old route still works.
  Picking up a key only helps (`Completable.ahead`). Opening a door is the one
  move that can strand the player, so the rules ask the checker first and
  refuse the move if it says no.
- `Game` packages a state with its invariant, so `Game.completable` holds for
  every state the game can be in, by construction.

If generation gives up, a hand-written fallback dungeon is used; its proof is
`decide` run by the kernel at compile time, and the status line says so.

Vocabulary is in `CONTEXT.md`; design decisions in `docs/adr/`.
