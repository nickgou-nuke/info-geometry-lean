# Focused Aitchison contingency verification

This check verifies the canonical finite contingency-table modules using the
repository's unchanged Lean toolchain and Mathlib commit. It is useful when
unrelated optional path packages prevent root Lake initialization. Its result
is a **focused native Lean check**, not certification of the full root package
or permission to bypass the repository's publication gates.

From the repository root, with the pinned Lean/Lake toolchain on `PATH`:

```bash
bash scripts/build/hydrate_pinned_mathlib_cache.sh
python3 verification/aitchison-contingency/check.py
```

The first command is the maintained cache hydration helper. The second also
accepts `--lake /absolute/path/to/lake` if the pinned toolchain is installed
outside `PATH`. It expects the pinned Mathlib and inherited package checkouts
to be present and clean; it does not change dependency manifests.

The verifier holds the maintained shared build lock, with the descriptor
inherited by compiler children. It checks the exact root/Mathlib toolchains,
Mathlib revision, inherited dependency revisions and clean source checkouts.
It discovers the canonical repository import closure of
`InfoGeometry.Probability.AitchisonContingencyAudit` and compiles that closure
in dependency order into a new output directory on every run. Existing root
and candidate `.olean` files are excluded from that local import path.

The final Lean audit inspects every declaration, including private and generated
constants, in these six owners:

- `InfoGeometry.Probability.AitchisonContingency`
- `InfoGeometry.Probability.AitchisonContingencyDimensions`
- `InfoGeometry.Probability.AitchisonContingencyProbability`
- `InfoGeometry.Probability.BipartiteLogCoupling`
- `InfoGeometry.Convex.LogSumExp`
- `InfoGeometry.Algebra.FiniteSpinAlgebra`

It requires the contract's named projection, uniqueness, and dimension theorems.
The runner also verifies that the entire local source closure is exactly these
six mathematical owners plus the audit module. The audit rejects introduced
axioms, unsafe or partial declarations, and any transitive
axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The Python runner
stops at the first failed compilation and checks that source, configuration,
and verifier hashes remain unchanged throughout the run.

Logs, `.olean` hashes, the complete audited declaration counts, commands,
timings, and a JSON receipt are retained under
`.artifacts/aitchison-contingency/check-*`. No cache or build directory is
deleted. The source contract and separate semantic-review scope are documented
in `docs/AITCHISON_CONTINGENCY_CONTRACT.md`.

The ordinary root check remains separate:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Probability.AitchisonContingencyAudit
```

Pre-commit and pre-push checks continue to use their existing repository
configuration. A successful focused result must not be reported as a successful
root build if that command is blocked by missing optional path packages.
