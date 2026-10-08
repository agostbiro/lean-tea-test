# Depend on Mathlib for the proofs

The proven core needs finite sets, graph reachability and well-founded recursion for the fixed-point checker. We depend on Mathlib at the tag matching the Lean toolchain that lean-tea pins (v4.31.0), fetched from the prebuilt cache, rather than writing those lemmas in core Lean. The cost is about 7.6 GB on disk and that the two dependencies must advance in lockstep: Mathlib master already needs a newer Lean than lean-tea pins, so upgrades wait for both. Dropping Mathlib later means rewriting the reachability lemmas, not the game.
