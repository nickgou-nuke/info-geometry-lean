# Zorn/Souriau source-review checkpoint

Date: 2026-11-24. Original baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
Integration base: PR #441 at `4c45f2bd932592fa86820f2e3360085f9e060c38`.

This records source inspection and scoped text gates. It is not a native Lean
compilation result or a transitive axiom certificate. The final native driver
records its actual status, commands, source snapshot, and logs in
`artifacts/zorn-souriau/native/result.json`. The publication gate is separate.

## Independent review

The parent and repository scout authored the sources. A separate mathematical
auditor inspected all six modules against their actual imported owners and the
pinned Mathlib source. A separate QA reviewer inspected the validation route,
critical declaration names, input snapshots, and the module-ownership audit.
Neither reviewer ran Lean or Lake, and neither claimed kernel acceptance.

PR #441 was published while this work was underway. A fresh exact-head
comparison found that its general left inverse and unit criterion have the
same native carrier, operator, and norm as the initially proposed left API.
The eight duplicate public left declarations were removed. The change now
inherits that owner and retains the eight genuinely additional right-action
declarations and the separate Ell-circular coordinate consumers. Its native
audit traverses dependencies of the actual resulting declarations; no parent
PR's publication is treated as a compilation certificate.

The mathematical review checked both conjugate-contraction orders, right-action
composition order, the unrestricted canonical Zorn carrier, the null converse,
the Ell-circular norm normalization, and transport through genuine operator and
matrix algebra equivalences. It also checked the typed action groupoid and its
nontrivial translation example, the signed bilinear pullback, the nonempty
finite partition laws, and the noncommuting regular-operator example.

The final cotangent source was re-reviewed after replacing manually proved
bilinearity fields with native `LinearMap` compositions. The scalar identities
are isolated in explicitly real private lemmas. The displayed evaluation
formula, pullback, and nonzero plane counterexample retain the same meanings.

## Reviewed source hashes and explicit public inventory

The counts below come from the maintained source inventory, not native
environment enumeration. The native audit additionally covers private and
generated declarations and reconciles their owner identities.

| Module suffix | Explicit public declarations | SHA-256 |
|---|---:|---|
| `Lie.SplitOctonionRegularInvertibility` | 8 | `72f57c0e6cd412dc43f155a62e7022cd4e6852a1c777deb1db68fa9ad3e9b7d9` |
| `Lie.ZornChiralCircularFourVectorOperators` | 14 | `7f648b8a02ac0c4b5c923325cc115b58b967d05c49b3aa88cc916d9dd9110a22` |
| `Algebraic.CartanSouriauActionGroupoid` | 6 | `425e058800cc74575d4cbde77355aa1599ee12e4fe383a051ec853c7eb36946c` |
| `Algebraic.CotangentBilinearGraph` | 13 | `fb278b38fd3388ed64481f186ae6f41aeda6d04d9bd401a6ba2f9c9c15946c98` |
| `Analytic.FiniteNegativeLogPartition` | 9 | `b79a963e6c19c511f01a15208b79a933547ba129d3c85d1cf3e8f6c0ef8c210e` |
| `Canonical.ZornSouriauIntakeChecks` | 11 | `7d6c759bec7a29f92b6cff1bd8ebcf38f1be7f966bbe6d10ec126ca6e32a6514` |

Total explicit public declarations: **61**. Driver SHA-256:
`20b2981e480428c0dcc7d60132a1f7761a86b87fa711679f3c5c3b7c9ac44115`.

## Scoped source commands and observed results

The following array names the exact six-file scope, from the checkout root:

```bash
owners=(
  lean/InfoGeometry/Lie/SplitOctonionRegularInvertibility.lean
  lean/InfoGeometry/Lie/ZornChiralCircularFourVectorOperators.lean
  lean/InfoGeometry/Algebraic/CartanSouriauActionGroupoid.lean
  lean/InfoGeometry/Algebraic/CotangentBilinearGraph.lean
  lean/InfoGeometry/Analytic/FiniteNegativeLogPartition.lean
  lean/InfoGeometry/Canonical/ZornSouriauIntakeChecks.lean
)
git diff --cached --check
python3 -B tools/quality/proof_proxy_staged_gate.py
python3 -B tools/quality/placeholder_audit.py --strict "${owners[@]}"
python3 -B tools/infra/axiom_audit.py --fail-on-gaps "${owners[@]}"
python3 -B tools/quality/repo_lean_scope_audit.py "${owners[@]}"
python3 -B tools/quality/semantic_content_audit.py \
  --file-prefix lean/InfoGeometry/Lie/SplitOctonionRegularInvertibility.lean \
  --file-prefix lean/InfoGeometry/Lie/ZornChiralCircularFourVectorOperators.lean \
  --file-prefix lean/InfoGeometry/Algebraic/CartanSouriauActionGroupoid.lean \
  --file-prefix lean/InfoGeometry/Algebraic/CotangentBilinearGraph.lean \
  --file-prefix lean/InfoGeometry/Analytic/FiniteNegativeLogPartition.lean \
  --file-prefix lean/InfoGeometry/Canonical/ZornSouriauIntakeChecks.lean \
  --gate --json-out /tmp/zorn-souriau-audit-20261124/source-semantic.json
```

All commands exited zero on the source hashes above. The staged proof gate
reported `ok`; the source axiom/debt and scope audits found zero open gaps.
The semantic audit selected six files and found zero findings. The placeholder
audit found zero hard findings and two soft short-proof flags:

- `signed_graph_scalar` is a polynomial identity over explicitly real inputs.
- `phaseVector_diagonal_det` specializes the native norm formula and changes
  multiplication to the conventional square notation.

Both short proofs were inspected at their actual scalar goals. The flags are
retained here; they are not native compiler warnings. Python AST parsing of
the driver also succeeded. This is not a Python test-suite result.

The new focused GitHub workflow parsed as YAML; each shell step passed
`bash -n`, and its embedded Python parsed with `ast.parse`. Its exact-head
checkout, read-only permissions, serialized driver, and retained evidence were
reviewed separately. No hosted workflow result is inferred from those checks.

## Native execution at this checkpoint

An initial diagnostic invocation of the maintained focused-package wrapper
requested the action-groupoid, cotangent, and regular-invertibility targets
with the exact pinned package-location overrides. It acquired the shared
lock and started Lake. Lake was terminated with return code `-9` (the outer
wrapper returned `247`) before any Lean success or proof diagnostic was
reported. The termination cause was not established.

No process belonging to another task was killed, no lock was removed, no
cache was deleted, and no toolchain or dependency pin was changed. The final
driver uses the same shared lock for the complete transaction and passes its
lock descriptor to children. Its fresh-source and native axiom stages remain
required even if a target build succeeds.

The theorem contract and evidence map state the mathematical boundaries.
This source-review checkpoint alone does not promote any new declaration to
`kernel_verified` and does not authorize skipping the publication hook.

## Native follow-up: determinant and nonzero incidence witness

The public revision `acbb4c0e8184478f502b400af94c19b23d08297c` contains
the repaired #442 sources from `8a0131dc39d5db88382ab931b66e5e4c26fab2fe`.
The complete artifacts from two native runs exposed the following remaining
proof elaboration and resource failures in these inherited sources:

- [Zorn/Souriau run 45406866380](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45406866380):
  the nonzero phase-vector witness expanded the coordinate transport too early,
  and the class-valued groupoid definition required `instance_reducible`.
  Artifact `14925594798` SHA-256:
  `0e733b916cb7e1248726207a0d2535da8428518f10c2ed0d1c796b753f0581d9`.
- [Split/Clifford run 45406866384](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45406866384):
  the 64-entry regular-matrix calculation reached its default heartbeat limit,
  and recursive cofactor expansion reached its existing finite 1,200,000 limit.
  Artifact `14927122918` SHA-256:
  `58786bc465b2e5a70f028516b0c70b0cc1e516f2b493d88bd445513f343d92d3`.

The matrix readout now compares the two actual linear actions using the native
`Matrix.toLin'` equivalence and eight generic coordinate identities. The
determinant uses Mathlib's `eval_det`, whose division-free Bird algorithm is
connected to `Matrix.det` by proved identities and kernel-checkable certificates.
The existing finite determinant budget is retained. No theorem statement,
hypothesis, coordinate order, or norm convention changes.

The nonzero witness first rewrites with the existing `phaseVector_coordinates`
lemma and `map_zero`, then evaluates the same embeddings. The concrete null
example and its nonzero conclusion are unchanged. The native groupoid witness
adds only the compiler-requested reducibility annotation.

Both candidates received independent mathematical and pinned-API source review.
Their reviewed SHA-256 values are:

| Source | SHA-256 |
|---|---|
| `CanonicalZornRegularExactDet.lean` | `903f274355a26e5b7220932620d330da318065ee28a411ffd8cb4175b5e4f0d1` |
| `ZornSouriauIntakeChecks.lean` | `6fd66915c97218cd68e0dff29ebc00943abb5a9f6f77cb0a507bb2e8f1e401aa` |

These changes require a new successful native receipt. The earlier failing
runs establish diagnostics, not acceptance.

The two repaired sources passed the staged proof gate, whitespace check,
scoped placeholder audit (zero findings), source axiom/debt and scope audits
(zero gaps), and semantic gate (two selected files, zero findings).
