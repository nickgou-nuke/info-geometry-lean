# Real Dirac incidence and Schur transport

A focused, pinned Lean package connecting four existing mathematical interfaces:
native real dual incidence, real spinor minors, finite bipartite edge operators,
and positive Schur-complement transport.

```lean
import InfoGeometry.Canonical.DiracPlabicCoarseAll
```

The [theorem contract](THEOREM_CONTRACT.md) records the exact carriers,
assumptions, conventions, and interpretation boundaries. See [RESULTS.md](RESULTS.md)
for the current validation state; the existence of this package is not evidence
that the root repository or every proposed physical interpretation compiles.

## Environment

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The focused manifest uses precisely the root-compatible Mathlib dependency pins.
- Real `.git`, `.lake`, and `.lake/packages` roots are required.

The package sources live in the canonical `lean/` tree. The package has its own
build output and shares the root `.lake/packages` directory. It does not modify
the root dependency manifest or substitute stubs for missing root path packages.

## Reproduce

From the repository root, with the pinned toolchain on `PATH`:

```bash
python3 verification/dirac-plabic-coarse/check.py exe cache get
python3 verification/dirac-plabic-coarse/audit.py
python3 verification/dirac-plabic-coarse/check.py build
python3 verification/dirac-plabic-coarse/check.py --strict-sources > dirac-strict.log
python3 verification/dirac-plabic-coarse/audit.py --log dirac-strict.log
```

The wrapper uses the maintained global build lock and keeps every compiler
invocation sequential. The strict mode rechecks all six new Lean files with
warnings treated as errors. The audit imports the public umbrella and reports
the transitive axioms of every explicitly named public declaration in the four
owners. The Python checker rejects inventory omissions, duplicates, unexpected
names, and any foundation outside `propext`, `Classical.choice`, `Quot.sound`.

The source inventory is intentionally bounded; it is not a general Lean parser.
Compilation, axiom dependencies, semantic review, and heuristic source screening
are distinct checks. Imported private helper dependencies are audited through
public declarations.

## Publication and recovery

The original unpublished local snapshot `24a9e94a` and its source revision
`0f7f2dc8` were unavailable after the transient workspace was reset. Their exact
bytes and archived QA logs could not be recovered from GitHub, saved artifacts,
or the accessible workspace. This PR contains a **fresh reconstruction** from
the established theorem contract and current native owners. It does not inherit
the earlier snapshot's compilation or acceptance certificate.

The user explicitly authorized draft publication with the root publishing gate
blocked by unavailable root path dependencies. No hook, dependency pin, or
shared-lock implementation is weakened by this package. Current results refer
only to the reconstructed files and are recorded separately.
