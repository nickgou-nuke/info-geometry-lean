# Schwinger operator bases: validation

Date: 2026-11-20. Source baseline:
`8ac42b1efaa7fe8ad92df3c5acadf0c3a3534ebe`.

Status: **independent local native and source-gate acceptance passed**.
The final source, including the explicit real matrix-unit noncommutativity
witness, passed a fresh build and declaration audit. Actual commit-hook
execution and published-head CI are separate publication steps, reported on
the PR; this record does not predict a future CI result.

## Accepted surface and environment

The three new selected owners are `InternalCubicWeylBasis`,
`RealCubicWeylBasis`, and `SchwingerIntertwiner`, all under
`InfoGeometry.OperatorAlgebra`. The focused workflow also retains the five
previous PR owners. The computed combined closure contains 33 repository
modules and 51 native import roots.

The run used Lean `leanprover/lean4:v4.34.1`, native compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All eight Mathlib package revisions
matched its manifest and were clean. A separate runtime agent performed all
compilation and cache operations under the maintained shared `BuildLock`,
without editing the proofs. No dependency pins or maintained quality-gate
implementations changed.

All **33 repository modules compiled afresh, with zero reused outputs**.
Every selected owner had **zero compiler warnings**. The independent audit
covered every owned declaration, including definitions and generated helpers:

| Selected owner | Audited declarations | Compiler warnings |
|---|---:|---:|
| `OperatorAlgebra.CyclotomicGradedAdjoint` | 16 | 0 |
| `OperatorAlgebra.InternalCyclotomicGradedAdjoint` | 5 | 0 |
| `OperatorAlgebra.RealCubicAdjointWitness` | 36 | 0 |
| `Geometry.MixedPairingNondegeneracy` | 17 | 0 |
| `InformationGeometry.ContrastMixedHessianBoundary` | 36 | 0 |
| `OperatorAlgebra.InternalCubicWeylBasis` | 50 | 0 |
| `OperatorAlgebra.RealCubicWeylBasis` | 20 | 0 |
| `OperatorAlgebra.SchwingerIntertwiner` | 34 | 0 |
| **Total** | **214** | **0** |

The axiom union is exactly `[propext, Classical.choice, Quot.sound]`.
These are the permitted Lean/Mathlib foundations; no new axiom, proof
placeholder, unsafe declaration, or `native_decide` bypass is introduced.
The coordinate equivalence has explicit inverse proofs; its basis is not
obtained by assuming the desired basis as a structure field. Real scalar and
finite-basis infrastructure remains explicitly noncomputable where required.

The closure contains **30 compiler warnings in unchanged dependencies**.
The placeholder audit separately records 12 soft `skeletal-proof` heuristic
findings, and the semantic gate records 20 nonblocking `trivial_surface`
warnings. Short native equality and transport proofs were inspected in source;
their successful kernel checks and complete axiom audit are distinct from
those lexical heuristics. The acceptance does not claim that every check is
warning-free.

## Source identity and independent review

The three new owners passed complete independent source review and a
hash-scoped review of subsequent repairs. The reviewers did not author the
source they accepted; the runtime acceptance agent authored none of the proofs.

| New owner | Accepted SHA-256 |
|---|---|
| `InternalCubicWeylBasis.lean` | `8a6288d6e747cb11e8b15bcfc728a42a251dbfa039241f81a6b1746344749b66` |
| `RealCubicWeylBasis.lean` | `a79745ade9bbc2acced6f1c85677908bc65e8b8f1b8083bf5c8012fb4fe46e23` |
| `SchwingerIntertwiner.lean` | `6d99a0f5ca157a4669a72ad1b3afb82cefc573451cd912b3b7d8045f9a65dfe4` |

The five earlier proof owners retain the hashes in the original validation
record and were freshly compiled and audited again. All 33 closure hashes
matched both the working source and the Git index. The new contract,
literature amendments, PDF provenance manifest, and expanded workflow received
independent review separately from the mathematical and native acceptance.

The final local native `report.json` has SHA-256
`79b98f2f874a22bc91599b2913973a327ba433f7284d9717adab44ff366ada2b`.
Its `local_revision` is the source baseline above, because the check ran
before the new commit. The content hashes identify the accepted new source
bytes; the report does not claim those bytes already existed in the baseline.

The index tree during the final native/source-gate transaction was
`aa23f63021fef659c4c8cd4fad6b31cf059ba766`. This documentation record was
completed afterward. Its final hash is bound separately before publication;
none of the accepted Lean source bytes changes when the record is completed.

## Executed checks

The working directory was
`/workspace/scratch/0878f2086cff/schwinger-operator-bases`. The actual native
command was the following, with the runtime's `python3` executable:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/0b027a897d29/lean_verification_runtime/mathlib4 \
  --lean /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lean \
  --output /workspace/scratch/0878f2086cff/schwinger-verification/acceptance \
  --target InfoGeometry.OperatorAlgebra.CyclotomicGradedAdjoint \
  --target InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint \
  --target InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness \
  --target InfoGeometry.Geometry.MixedPairingNondegeneracy \
  --target InfoGeometry.InformationGeometry.ContrastMixedHessianBoundary \
  --target InfoGeometry.OperatorAlgebra.InternalCubicWeylBasis \
  --target InfoGeometry.OperatorAlgebra.RealCubicWeylBasis \
  --target InfoGeometry.OperatorAlgebra.SchwingerIntertwiner
```

It returned exit code 0. Neither `--incremental` nor an audit-skipping option
was used. Scoped cache recovery used precisely the 51 native import roots
under the build lock; it decompressed existing cached artifacts, downloaded
nothing, and changed no pins. Failed prerequisite and source-gate attempts
were preserved separately from the final accepted run.

The maintained source checks all returned success:

| Check | Actual coverage and result |
|---|---|
| `placeholder_audit.py --root PATH --strict` | Eight separate commands, one per selected owner; 0 hard findings, 12 soft heuristic findings. |
| `semantic_vacuity_gate.py PATHS --fail-on error` | All eight exact paths read, complete coverage, no read failure, 0 errors, 20 nonblocking warnings. |
| `opengauss_cli.py refute PATHS --strict --json` | All eight files `PASS`, no traps. |
| `opengauss_cli.py review PATHS --gate GATE_4 --json` | All eight files `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; the separate native check supplies kernel evidence. |
| `proof_proxy_staged_gate.py --strict` | The three newly staged Lean files passed. |
| Explicit `ActiveIndexCache` / `check_text` with `strict=True` | All eight target blobs read from the index, equal to the compiled working bytes; zero violations and no index mutation. |

`PATHS` denotes the eight fully qualified modules in the native command,
converted to `lean/` paths with `/` in place of `.` and a `.lean` suffix. Raw argument
arrays, exit codes, stdout/stderr, per-file logs, the complete native report,
and the acceptance receipt are retained in the local acceptance directory.
The explicit indexed-content check ensures that a clean CI index cannot
silently skip the five previously tracked owners.

An initial T16 source-gate finding was resolved by
`real_matrix_units_noncommute`, the proved `E₀₁`/`E₁₀` noncommutativity
witness on the actual native real matrix basis. The gate was not modified or
exempted. The final fresh build and every source gate include that witness.

## Evidence boundaries

- Repair runs used fingerprint-matching dependency artifacts; the final
  acceptance above used none of those outputs.
- The source PDF was read directly from the user-supplied attachment. Its
  byte length and hash identify the original; the PDF is not copied into the
  repository. CI binds the manifest and contract to the evidence index, not
  a newly downloaded or reconstructed copy of the paper.
- The prior five-owner record remains at
  [UNIFIED_OPERATOR_BRIDGES_VALIDATION.md](UNIFIED_OPERATOR_BRIDGES_VALIDATION.md).
  A scoped result is not a repository-wide build result.

The focused workflow repeats the fresh check on the exact PR head, requires
the report revision to equal that head, verifies all eight target inventories
and the full import closure, and publishes reports, logs, and audit source in
`unified-operator-bridges-kernel-evidence`. It binds the workflow, maintained
helpers, dependency pins, contracts, literature ledger, validation records,
and intake manifests to evidence hashes. A successful future run and its
artifact reconciliation are reported on the PR, not asserted prospectively
by this local record.

The full real basis is algebraic. This acceptance does not establish its
orthonormality for the standard transpose or a compatible positive weighted
metric. The seeded identity for a supplied conjugator does not construct an
unknown conjugator from abstract multiplication-table-equivalent bases.
The finite results also supply no analytic infinite-dimensional limit.
