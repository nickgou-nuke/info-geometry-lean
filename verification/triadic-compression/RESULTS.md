# Verification record: tripotent compression

## Accepted implementation and exact source base

- Base commit: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
- Verified implementation commit: `5d9c0d4dd823a2978106556dcd901542faecc659`.
- Independent QA-A verdict: **PASS**, completed `2026-11-12T12:36:54.461561+00:00`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine selected dependency checkouts match the root and focused pins and
  have clean tracked sources.
- All 21 protected source/configuration files matched their committed bytes
  before and after verification. Implementation HEAD remained unchanged.

The final delivery adds documentation only after this acceptance. Its proof,
audit, runner and configuration bytes are checked against the accepted hashes
when the review package is assembled. The delivery commit is recorded in the
package's `SOURCE_MANIFEST.json`.

## Independent review and static checks

- A-A semantic review: PASS for the mathematical contracts, arbitrary real-Hilbert
  common-kernel criterion, native audit, source-bound driver, and the documented
  distinction between pointwise strict positivity and uniform coercivity.
- QA-A independently reviewed and executed the checks without authoring or
  modifying the protected implementation.
- Staged proof proxy gate: exit 0.
- Vacuity linter on the six touched mathematical modules: no findings.
- Placeholder/custom-axiom/unsafe/partial/native-decide scans: no findings.
- Staged whitespace check: exit 0.
- Ten nonblocking Lean linter warnings were recorded: unused section assumptions,
  an unused simp argument, and unnecessary `simpa`. No compiler failure occurred.

## Actual compiler and fresh audit results

The independently executed driver was:

```bash
PATH=/home/agent/.elan/bin:$PATH python3 verification/triadic-compression/audit.py
```

The driver exited **0**, with result **PASSED**. Its two subprocesses used the
existing workspace-integrity check and the shared build lock:

| Check | Actual exit code | Recorded wall duration |
|---|---:|---:|
| Focused build of `InfoGeometry.Core.TripotentCompressionAudit` | 0 | 5523.608 seconds |
| Fresh `env lean` invocation on the absolute audit source | 0 | 3810.836 seconds |

These durations include substantial waiting for the global build lock; they
are not compiler-performance measurements. The driver ran from
`2026-11-12T10:00:32.957881+00:00` to `2026-11-12T12:36:08.028159+00:00`.

All **67 new mathematical theorems and lemmas** compiled. The complete selected
owner inventory contains **268 declarations**, including
**243 theorem declarations** and generated helpers.

| Selected owner | All owned declarations |
|---|---:|
| `InfoGeometry.Core.CornerCentrality` | 7 |
| `InfoGeometry.Core.PeirceCompressionCStar` | 5 |
| `InfoGeometry.Core.PeirceCompressionDefect` | 62 |
| `InfoGeometry.Core.PeirceDecomposition` | 60 |
| `InfoGeometry.Core.TripotentCompression` | 11 |
| `InfoGeometry.Core.TripotentCompressionCStar` | 5 |
| `InfoGeometry.Core.TripotentCompressionHilbert` | 10 |
| `InfoGeometry.OperatorAlgebra.TriadicCompressionCounterexample` | 55 |
| `InfoGeometry.Physics.Algebra.TripotentPeirceProjectors` | 53 |

## Axioms and actual dependency graph

Both runs emitted identical complete declaration inventories and identical
native graphs. QA independently parsed all 268 complete bracket arrays,
including the 129 multiline arrays; the following counts refer to declarations
whose transitive dependencies include the named foundational axiom:

| Allowed foundational axiom | Declaration usage count |
|---|---:|
| `Classical.choice` | 124 |
| `Quot.sound` | 129 |
| `propext` | 239 |

No other axiom occurred. The allowed foundational axioms are ordinary Lean
foundations, not added physical or ontological assumptions.

The native audit extracts direct references from declaration types and
proof/definition values, including opaque theorem values. The selected-owner
graph has **552 unique edges** on **268 nodes**.
Every endpoint is in scope. The runner's deterministic topological ordering
was independently checked, and an independent depth-first traversal found no
cycle. Both required proof-body edges were observed. An edge means
`dependency -> dependent`, not a physical causal implication or a Hasse cover.

This is the induced graph for the nine named owners. It is not a complete
repository graph, a new Lean theorem constructing a `PartialOrder`, or a
classification of all possible models. Other source-reviewed branches named
in the theorem contract are not newly certified by this nine-owner audit.

## Inspectable acceptance evidence

The review package includes the complete compiler/audit logs and:

- `evidence/validation.json`: source-bound native inventory and full graph;
  SHA256 `06bd198eb451e57e541374086ddc10a42a0cf545853515df4419bf41eede6511`.
- `evidence/qa-acceptance.json`: the separate independent acceptance record;
  SHA256 `94ad53290c3406f810e658c35feb2a1b6caa9cecbb6d29f7590a4b124d7a685d`.

The runner intentionally leaves its own `independent_qa_acceptance` flag false:
independent acceptance is supplied by the separate QA record, not self-issued
by the driver. That record checks log hashes, committed source bytes, pins,
complete axiom arrays, graph equality, and the topological order.

## Root integration and publication scope

The focused package reads the canonical repository sources in `../../lean`
with the exact root Lean/Mathlib revisions. It does not replace any owner or
import, stub a dependency, modify a root pin, or waive a publication gate.

A separate root invocation already stopped while resolving the inherited path
dependency `external_refs/homotopy-hypothesis-lean4`, which is absent in this
checkout. This record therefore makes no whole-repository success claim.

The review package carries a separate `evidence/pre-push-result.json` for its
exact delivery commit, with the actual installed hook invocation, output,
exit code, and source/HEAD stability. This focused mathematical acceptance is
not a substitute for that required gate. Remote publication is reported
separately from proof verification.
