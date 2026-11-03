# Verification

`scripts/verify.py` builds every maintained `Blotto/*.lean` module, checks that
`Blotto.lean` imports them all, verifies the exact compiler/dependency pins and
clean dependency checkouts, rejects source proof escapes, and inspects the
compiled environment. The environment audit includes private helpers and
generated safe declarations. Compiler-generated `_unsafe_rec` implementations
are recorded separately; they are not presented as safe logical declarations.

The only accepted axioms are `Classical.choice`, `Quot.sound`, and `propext`.
Logs and full receipts are generated under `build/verification/` and are ignored
by Git. `scripts/check_coverage.py` checks every declaration in the public map
against the current verified source. Neither tool automatically proves the
correspondence between English statements and Lean statements.

`scripts/replay_endpoints.py` invokes the pinned built-in `leanchecker` on one
exact endpoint module at a time. The imported environment is the starting point;
this is not a fresh replay of every transitive dependency or a separate kernel
implementation. Lean's `-t 0` axiom audit alone does not re-typecheck imports.

Heavy jobs share a lock, use bounded worker counts, and have a process-group RSS
watchdog and system-memory reserve. Monitoring must be available before a job
can start. RSS is sampled every quarter second, so this is not an OS hard limit.
Do not run bare `leanchecker`, `leanchecker Blotto`, or `leanchecker --help` with
this pinned toolchain: unknown flags are ignored and the default selects a large
parallel replay. Use the supplied script instead.

The scope of cost verification is described in
[cost-correspondence.md](cost-correspondence.md). The paper's proofs were reviewed
against the formal endpoints, including hard at-most budgets, zero ties,
independent whole-player laws, and deviations in the continuous game.
