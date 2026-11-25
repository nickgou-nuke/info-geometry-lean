# Independent verification-path review

Reviewer: separate `klein_validation_review` agent, distinct from the source
authors and the mathematical reviewer. Review date: 2026-11-24.

**Disposition: source/provenance review complete; native QA remains blocked.**
This is not a kernel-check certificate or repository acceptance.

The reviewer read the current sources, source imports, Git metadata, hashes,
dependency metadata, and saved run receipt. The reviewer did not run Lean,
Lake, tests, proof gates, or the axiom audit, and did not change tracked owners,
caches, the shared lock, or GitHub state. This report is the only authored file.

## Reviewed snapshot

Checkout: `/tmp/info-geometry-zorn-primal-dual-20261124`.
Parent commit: `98587ebd1e5194d43753b55f1501c57f1478a11c`.

| File | SHA256 |
| --- | --- |
| `lean/InfoGeometry/Algebra/ZornNullIncidence.lean` | `93c03658e0a7049f481bed255fbdb998cb00ac4e6bbb5b4f7162df34f11bd8e4` |
| `lean/InfoGeometry/Canonical/ZornCliffordKleinHierarchy.lean` | `ea37f4082661ebee3c7519e290509c0162e51b9e4e2f61acca76e1db436cc5ba` |
| `lean/InfoGeometry/Canonical/ZornCliffordSourceVolume.lean` | `cfe9cb440f28021fbfc8a572355ca4d691133cae4e5a89e58494e7df890c6058` |
| `lean/InfoGeometry/Lie/SplitOctonionNullPlaneCovariance.lean` | `43e69c589182d5eace8bf194b59648f7b110fb1549759d1805c0bef9e80346bd` |
| `verification/zorn-primal-dual/check.py` | `293bd44367d8594ae9f51d8f9a148ca90e8a28cc8fa61e112aa3e5658a7a2ca5` |
| `verification/klein-operator-hierarchy/Audit.lean` | `db2f5841066eada24f0bac3900e73db41f20660c5d99ff4542ce02856d06bf5b` |
| `lake-manifest.json` | `ceb11ec7ca6c59a1d7787a9bb90a46c8fed69f1b751ee1834ea6a446c92cec98` |

The four integrated owner hashes match the frozen source-review snapshot.
The public `InfoGeometry.All` source imports all four owners. This is an import
inspection, not an elaboration of the umbrella.

An independent read-only traversal of the four target imports found **25
repository modules**. Every import encountered in that bounded closure uses
one unqualified `import` and one module name per line, matching the checker's
documented parser. No claim about import syntax outside this closure is made.

## Verification-path findings

- The selected suite has exactly the four new targets, its own output
  directory, and its own audit file. The default original suite is preserved.
- The maintained exclusive build lock remains in the execution path.
  The no-wait option cannot turn lock contention into a successful result.
- The checker records the compiler version and binary hash, dependency
  revisions and paths, manifest hash, checker hash, source hashes after lock
  acquisition, and the audit hash after lock acquisition. It revalidates the
  environment and source hashes before reporting completion.
- The checker now distinguishes an expected but unrun audit from an audit
  omitted by an explicit target override. A compiled subset is therefore not
  implicitly an audited full suite.
- The child-wait exception path now terminates and reaps only the child
  launched by that invocation before leaving the lock scope. Repeated SIGINT
  is ignored during that cleanup and the prior handler is restored afterward.
  This repairs the identified normal-exception path in which the parent could
  previously unlock while its child remained active. The repair was inspected,
  not exercised by a lifecycle test.
- The audit selects all available declarations attributed to the four new
  owners and the reused `Canonical.ZornCliffordRepresentation` owner. It
  rejects unsafe/partial declarations, requires a positive declaration count
  for every selected module, and restricts transitive axiom dependencies to
  `propext`, `Classical.choice`, and `Quot.sound`.
- The pinned Lean implementation of `Lean.collectAxioms` was inspected. It
  collects transitive dependencies; imported declarations use exported axiom
  metadata. The prepared audit has not been executed.

No remaining concrete verification-path source blocker was identified in
this review scope. That finding does not establish successful runtime behavior.

## Independently inspected blocked receipt

Read both the latest receipt and its identically matching unique file:

- `.lake/klein-operator-hierarchy/report.json`
- `.lake/klein-operator-hierarchy/report-ee0a176fa88149a985efe2f8435dd7f6.json`

Recorded run ID: `ee0a176fa88149a985efe2f8435dd7f6`.
Recorded time: 2026-11-24 10:43:12–10:43:13 UTC
(12:43:12–12:43:13 Europe/Sofia).

| Receipt field | Observed value |
| --- | --- |
| `status` | `blocked` |
| `suite` | `klein-operator-hierarchy` |
| `targets` | The four targets listed above |
| `wait_for_build_lock` | `false` |
| `force` | `true` |
| `commands` | Empty array |
| `audit_expected` | `true` |
| `audit_status` | `not-run` |
| Lock owner | `real-matrix-split:83` |

The inspected checker returns exit code 2 for this blocked path. The author
also reported observing exit code 2. This reviewer did not rerun that command.

The receipt's checker hash matches the reviewed checker. Its manifest hash
matches the current manifest. The recorded compiler is Lean v4.34.1,
compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`. Independently
hashing the named compiler binary matched the receipt's SHA256:
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.

For all eight recorded package search paths, independent Git metadata reads
confirmed that the current revision matches both the manifest and the receipt,
tracked package sources are clean, and those paths do not contain an
`InfoGeometry` namespace directory. The Mathlib revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
These are source/environment metadata checks, not a rebuild or certification
of every cached dependency artifact.

The blocked run stopped before the checker's source-snapshot and audit-hash
stage. Consequently, that receipt contains neither compiled-module results
nor a source-hash/audit-hash certificate. The current source and audit hashes
are recorded separately in this review. **No Lean elaboration or axiom audit
began in this run.** The environment version probe is not elaboration.

## Remaining acceptance work

Native elaboration and any resulting proof/linter repair, actual execution of
the declaration audit, independent native QA, the original PR suite, and the
repository's separate precommit/prepush/integration checks remain outstanding.
Neither this review nor the blocked receipt certifies the four new modules,
the earlier draft owners, the public umbrella, or the whole repository as
compiled.

The source hashes in this report were independently compared with the staged
blobs after the parent froze the current fourteen task paths. All four owner
files, the checker, and the audit match both the reviewed worktree bytes and
the index bytes. The parent remains responsible for matching the published
commit to that snapshot and for adding this report if desired.
