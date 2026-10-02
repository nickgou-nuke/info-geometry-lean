# Declaration dependency bridge

## Scope

`lean/InfoGeometry/Meta/DeclarationDependencyBridge.lean` extends the existing
finite dependency compiler. It does not introduce a new scheduler, proof search
engine, database, or QMS promotion worker.

The dependency order is:

1. A partial order on nodes and an injective assignment of Lean declaration names.
2. An explicitly supplied dependency relation and a resolution witness for every
   dependency of every represented target.
3. The existing valid schedule and certified compilation.
4. Named dependency closure and proof availability at every schedule prefix.

`DependencyCorrespondence.resolve` requires a represented, strictly earlier
source for each supplied dependency. The partial order may conservatively include
more precedence constraints than the supplied relation. Self-dependencies cannot
satisfy this interface. Dependencies outside the represented nodes must not be
silently omitted when constructing a correspondence for a real environment.

The main theorem, `certified_compilation_preserves_named_dependencies`, derives
the executable schedule, its permutation property, absence of backward dependency
edges, final environment coverage, and prefix closure with proof availability.
It reuses `compileCertified_sound` and the existing prefix-preservation lemmas.

## Regression slice

`lean/InfoGeometry/Meta/DeclarationDependencyBridgeTests.lean` assigns nodes to
the existing `validSchedule_fresh` and `validSchedule_nodup` declarations. Its
statements are their actual propositions specialized to natural-number nodes,
not assertions about index bounds. Proof rules reuse the existing proofs.

The selected dependency edge is explicit, not automatically extracted. Tests
cover reordered input, duplicate rejection, a missing prerequisite, failure of
closure for a target-only environment, and proof-preserving prefixes.

## Verification

Source is staged; compilation and axiom auditing are pending. At implementation
time, the shared lock was held by the main `lake build -R`. No concurrent Lean
process was started for this change.

After inspecting running compiler processes, verify through the shared lock:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Meta.DeclarationDependencyBridgeTests
```

The test module includes `#print axioms` for the main bridge theorem and its
concrete certified-compilation example. Their output must be reviewed before
claiming kernel verification.

## Checked-environment extension

`EnvironmentDependencyBridge.lean` defines dependency edges using checked kernel
declarations and the existing `DAG.edgesFromConstantInfo` extractor. Its
correspondence requires an explicit, present, dependency-closed baseline for
imports and an ordered resolution witness for dependencies outside that baseline.
The theorems transport named closure to the actual environment relation, including
the baseline, and retain proof availability after certified compilation.

This is a conditional theorem over that extractor's relation, not a proof that
all Lean kernel implementation dependencies have been modeled by the extractor.

## Native contract audit

`KernelContractAudit.lean` adds process-local `capture`, `audit`, and
`requireAdmission` operations. They reuse the repository dependency traversal,
Lean's transitive axiom collector, and the existing strict admission policy.
`StrictSurface.auditExistingDeclaration` shares that policy with the existing
strict declaration commands rather than replacing it.

The audit:

- Rejects changed or missing declarations from the captured checked environment.
  Payload comparisons include recursor/inductive metadata; no hash is trusted.
  Lean's payload equality treats alpha-renaming of expression binders as equal.
- Requires root coverage and closure under the existing dependency extractor.
- Checks the requested declarations are checked theorems and the supplied types
  are closed propositions definitionally equal to their declaration types.
- Rejects unsafe/partial dependencies and axioms outside `propext`,
  `Classical.choice`, and `Quot.sound`.
- Checks the proposed order against extracted transitive dependencies between
  selected targets; this is a validator, not another scheduler.
- Reuses QMS hard checks, proof-shape review, and region policy. Only
  `requireAdmission` requires every verdict to be `admitted`; `audit` can return
  review/blocked verdicts and is not permission to promote.

Native command entry points accept parallel declaration and proposition lists:

```lean
#audit_epistemic_schedule [firstLemma, secondLemma] against
  [firstProposition, secondProposition]

#require_epistemic_admission [firstLemma, secondLemma] against
  [firstProposition, secondProposition]
```

`EpistemicPipelineTests.lean` runs the existing compiler on a two-node order,
maps the result to a genuine natural-number theorem chain and independently
elaborated specifications, and exercises the native audit. Negative tests cover
stale evidence, mismatched statements, missing coverage, reversed dependencies,
duplicates, open/non-propositional specifications, empty requests, and QMS review
being insufficient for admission. A deliberately corrupted snapshot in a negative
test is never installed into Lean's current environment.

Verify this extension, after checking compiler processes, with:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Meta.EpistemicPipelineTests
```

## Remaining operational boundary

The extension is staged source, **not yet compiler-verified**: the main build
still holds the shared lock. No new compilation was started concurrently.

The native audit is a metaprogram with regression tests, not a proved correctness
theorem about Lean's kernel or its metaprogramming implementation. Formal
correspondence witnesses are not automatically synthesized from its reports.
Snapshots are in-memory checked environments, not signed certificates or disk
freshness checks. A new process must load freshly built imports after source,
toolchain, or dependency changes. The external QMS/hive worker must still bind
that run to current source/build artifacts before filesystem or database promotion.
Neither command uploads, commits, promotes database packets, or validates a
natural-language interpretation of the supplied proposition.
