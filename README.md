# Colonel Blotto in Lean

Lean 4 formalization and source implementation accompanying **Efficient
Equilibrium Computation in Colonel Blotto Games**, by Martin Bichler and
Abheek Ghosh.

The library covers the common-value exact coupling construction, its finite-bit
approximation, the general common-value FPTAS, and the conditional extension to
player-specific values. The game has hard budgets on every allocation,
allocations spending at most the budget, independent player randomization, and
equal sharing of ties, including zero ties. Equilibrium guarantees cover all
feasible continuous deviations.

## Build and check

Use the exact Lean toolchain and dependency revisions shipped in `lean-toolchain`
and `lake-manifest.json`: Lean **4.34.1**, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

```sh
git clone git@github.com:AbheekG/colonel-blotto-lean.git
cd colonel-blotto-lean
python3 scripts/prepare_dependencies.py
python3 scripts/verify.py
python3 scripts/check_coverage.py
python3 scripts/replay_endpoints.py
```

Python 3.11+ and a POSIX Linux/macOS environment are required by the verification
scripts. Dependencies can be reused when their pins match. Preparation fetches
only the required Mathlib import closure. The standard library target is `Blotto`;
with dependencies installed, `LEAN_NUM_THREADS=1 lake build` also builds it.

The scripts monitor memory, serialize heavy verification jobs, and stop above
6 GiB sampled process-group RSS or below 4 GiB estimated system-memory headroom.
The watchdog checks headroom before starting. A stopped check is not a pass.
See [verification details](docs/verification.md).

## Main results

| Result | Formal entry point |
| --- | --- |
| Common-value exact construction | [`PaperPRGExactTheorem.paper_theorem`](Blotto/PaperPRGExactTheorem.lean) |
| Common-value finite-bit approximation | [`PaperPRGFiniteCorollary.paper_corollary`](Blotto/PaperPRGFiniteCorollary.lean) |
| General FPTAS | [`GeneralPaperFirstAlgorithmContract.actual_contract`](Blotto/GeneralPaperFirstAlgorithmContract.lean) |
| One battlefield, exact case | [`GeneralPaperOneFieldExact.bit_exact`, `.real_exact`](Blotto/GeneralPaperOneFieldExact.lean) |
| Player-specific exact construction | [`PlayerSpecificRealAlgorithm.actual_contract`](Blotto/PlayerSpecificRealAlgorithm.lean) |
| Player-specific finite-bit construction | [`PlayerSpecificFiniteSamplerEveryDrawContract.finite_bit_contract`](Blotto/PlayerSpecificFiniteSamplerEveryDrawContract.lean) |

All names are in namespace `Blotto`. The [coverage map](docs/paper-coverage.json)
lists all 18 named paper statements, supporting claims and model definitions.
This is a Lean library; no standalone command-line equilibrium solver is supplied.

## Verification scope

The proofs establish the formal algorithms' distribution, budget and equilibrium
contracts and bounds on explicitly defined operation traces/work functions.
The audit checks safe compiled declarations, including private helpers, and
permits only `Classical.choice`, `Quot.sound`, and `propext`. Endpoint replay
rechecks each selected module's new declarations relative to its imports.

The remaining work is a complete machine-checked correspondence between all
implementation operations and their cost accounting in the paper's abstract
computational models. That limitation does not identify a known incorrect
output or cost undercount. See the [cost-correspondence status](docs/cost-correspondence.md).
Generated compiler code, garbage collection and physical stack costs are outside
these abstract-model claims.

## Citation and license

Citation metadata is in [CITATION.cff](CITATION.cff). A license for the original
implementation has not yet been selected. Lean and Mathlib dependencies retain
their own licenses and are obtained separately.
