# Prove completability with a verified checker, not a verified generator

The headline theorem is that every dungeon the game produces is Completable and every legal move keeps it so. We attach the proof to a checker rather than to the generator: the generator is ordinary unproven code that may use the RNG freely, a separate checker decides reachability of the Stairs with keys, and the game only accepts dungeons the checker approves, re-rolling on rejection. The proof obligations are checker soundness and move preservation. We chose this over a correct-by-construction generator because the checker is small, its proof survives generator rewrites, and it will be reused as-is when consumable keys are added. The cost is that generation termination and rejection rate are not proven.

## Considered Options

- Correct-by-construction generator carrying an invariant at every step. Rejected: every generation step needs a proof, the RNG threads through proof-carrying code, and any generator change redoes proofs.
- Both: invariant on the room graph, checker on the final grid. Deferred: may be worth it if rejection rates turn out high.
