# Gated Arango dependency export

Implementation: `lean/InfoGeometry/Meta/ArangoDependencyExport.lean`.
Validation status: source added; Lean verification is pending the shared build lock.

Use an existing `HiveBridge.PreparedPlan` with an independently reviewed
declaration/type contract and the existing finite dependency scheduler. Call
`ArangoDependencyExport.exportPlan plan` for JSON or `emitPlan plan` to log it.
Both rerun `KernelContractAudit.requireAdmission` through `withAdmission`.
Missing declarations, forbidden axioms, incomplete dependency closure, stale
process-local evidence, invalid schedules, and QMS review/block decisions prevent
export. No theorem-name-only command fabricates a specification or admission.

The adapter reuses `DAG.edgesFromConstantInfo`, including type references,
projection heads, and opaque values. It exports the audited dependency closure
without an `InfoGeometry` namespace filter. Edges point from dependent to
prerequisite and retain their type/value role, including self references.
Vertices are sorted by declaration name, not claimed to form a topological
schedule. Only `scheduled_targets` carries the existing plan's audited ordering.

Vertices are labelled `kernel_environment_declaration`, not `QMS_Verified`.
The target admission reports are retained separately. A theorem's hypotheses
remain visible in its type; admission and serialization do not discharge them.
In particular, a detector/spectral resonance hypothesis is not a proof of
Selberg's conjecture or RH.

Keys use Lean's bounded name hash, with collisions rejected within each payload.
These are identifiers, not cryptographic proof commitments. A database consumer
must also compare stored declaration identities before any cross-payload upsert;
the within-payload check does not establish global collision freedom. The adapter
does not create collections, contact ArangoDB, or upsert documents.

`promotion_allowed` is always false. JSON/log output is not authenticated kernel
evidence. Process provenance, disk/import freshness, database authorization,
replay protection, and operational promotion remain separate gates. The exporter
does not replace `DAG.ExprArangoExport` for expression-level graph export or the
existing ingestion tools.

Regression target: `InfoGeometry.Meta.ArangoDependencyExportTests`. Its rejection
case ensures that a QMS-review theorem cannot be exported through this adapter.
