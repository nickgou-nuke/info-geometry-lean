# Courant / cotangent / neutral-graph validation

Status: **PASS for the focused exact-pin source compilation and native declaration audit.**
The separate root Lake build remains unverified; its observed failure and the
independent dependency-provenance findings are recorded below.

## Source and environment

- Repository baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
- Lean: `leanprover/lean4:v4.34.1`.
- Observed compiler release commit: `5045d0056413266e57c625dcd7c365b10e377c52`.
- Observed Lean executable SHA-256:
  `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The repository toolchain, manifests, and dependency configuration are unchanged.
- Four substantive owners are imported by
  `InfoGeometry.Geometry.CourantDrinfeldDiracCapstone`.
- One import in `InfoGeometry.All` exposes that aggregate through the existing
  public surface; the root `InfoGeometry` already imports `InfoGeometry.All`.

## Focused compiler scope

The reproducible check is:

```bash
python3 verification/courant-dirac/verify.py \
  --mathlib /workspace/scratch/3288f93e1961/validation \
  --work /workspace/scratch/3288f93e1961/check-final \
  --lake /tmp/dirac-toolchain-18ec/lean-4.34.1-linux/bin/lake \
  --wait
```

The completed transaction called `main(existing_lock=lock)` from the serialized
validation session, with the same arguments shown above. This supported
in-process entry point reenters the maintained exclusive lock and performs the
complete check; it does not reuse earlier compilation results or skip checks.
The verifier returned normally with status `PASS`, and all 12 child commands
(environment probe, version check, nine compilations, and audit) exited 0. The
validation session then exited 0 and released its lock. The standalone CLI
above runs the same acceptance path while acquiring its own lock.

The runner verifies the compiler,
Mathlib and eight dependency pins, snapshots the exact owner-source bytes,
compiles the complete nine-module project source closure, and binds imported
artifacts to those compilation receipts. All four new owners and the import-only
aggregate are compiled with warnings treated as errors. The four unchanged
dependencies are compiled in full, including their inherited imports.

The native audit enumerates declarations by Lean module ownership, including
generated declarations. It rejects unsafe, partial, and custom-axiom owners,
and uses `Lean.collectAxioms` to check transitive dependencies. The only allowed
foundations are `propext`, `Classical.choice`, and `Quot.sound`. An independent
parser reconciles the complete inventory with the module and summary records.

The native inventory and independent parser agree on **108 declarations**,
including generated declarations:

| Owner module | Declarations |
|---|---:|
| `InfoGeometry.Geometry.CotangentUnitLinearization` | 26 |
| `InfoGeometry.Geometry.MatrixDiracGraphs` | 24 |
| `InfoGeometry.Geometry.SkewGraphNeutralPairing` | 16 |
| `InfoGeometry.Lie.CotangentLieAlgebra` | 42 |

The exact transitive axiom union is `Classical.choice`, `Quot.sound`, and
`propext`. No owned declaration is unsafe, partial, or a custom axiom. No
transitive axiom outside the whitelist was found.

Native audit log SHA-256:
`169bd3d496b467d8672e474930111e79127ed753c1d21c74b0fa6c6b58f00d74`.

### Exact compiled sources

These hashes bind the original source files, copied compiler inputs, and
recorded artifact receipts. The verifier checked them before and after the
transaction, including every imported project artifact immediately before use.

| Module | Source SHA-256 |
|---|---|
| `InfoGeometry.Algebra.FiniteSpinAlgebra` | `9007f5e058a9662df00bce7cc59df337754013c271ec26ac446e139442de1567` |
| `InfoGeometry.Meta.Architecture` | `0f74caea1284e1c0dfc8d00d46357e0310a24aa12fc36fa7c0d02ef5f97e0434` |
| `InfoGeometry.Clifford.NeutralPhaseSpaceCore` | `1e9af32b34ffef78d0bc93a446abd1f90fb8d7b58583db10efc39aba46cf2093` |
| `InfoGeometry.Lie.CotangentLieAlgebra` | `39f7acaad523ee81a798ccbc8de7eb295b25c369bdc1ab6c63b3b18d6b4530fe` |
| `InfoGeometry.Canonical.SouriauKKSForm` | `3f48a07f7791c4127ffd166bb4557af47d7d4c0da621258f2d1d282ff7f0171c` |
| `InfoGeometry.Geometry.CotangentUnitLinearization` | `1faf046b416e15d1acf6fffd7fadc7ebdbb9b4030c6ca64e63d92390ab23ac07` |
| `InfoGeometry.Geometry.SkewGraphNeutralPairing` | `3e823559b3be812646619c60a2dcdc40c2e2f2de90f7b5ef545c8c0d1fc5b246` |
| `InfoGeometry.Geometry.MatrixDiracGraphs` | `07fe9bfc4410845f7a763afc40cdda884a85a590230128e5ed4e91b6d03230d8` |
| `InfoGeometry.Geometry.CourantDrinfeldDiracCapstone` | `5ce030234bffcec556f72cc8ff818b78e7562d938165be34ed621fe6f8a2701e` |

The complete machine receipt was written to
`/workspace/scratch/3288f93e1961/check-final/validation.json`; compiler and audit
logs are under its sibling `logs` directory. These are session-local evidence
paths. The committed checker and source hashes make the check reproducible in
another checkout with the same dependencies.

Independent final evidence review: **PASS**. See [FINAL_QA.md](FINAL_QA.md).
The reviewer independently reconciled all command/log receipts, source and
artifact identities, control fingerprints, clean dependency pins, native audit
records, final staged-gate evidence, and the documentation scope.

## Source review and repository gates

The claim ledger is in `THEOREM_CONTRACT.md`; independent mathematical reviews
and their source hashes are in `SEMANTIC_REVIEW.md`.
The pending-compiler notes in that historical review record describe the
scope of those reviews; the subsequent compiler and axiom result is the PASS
recorded above.

The full staged source gate passed after all graph and matrix proof repairs
and the intake/status documentation update:

```text
python3 tools/quality/proof_proxy_staged_gate.py
proof_proxy_staged_gate: ok
exit: 0
```

The check used all tracked `lean` and `proofs` source trees, materialized from
the baseline. The initial sparse-checkout attempt had reported missing tracked
imports; expanding the checkout resolved those missing-file reports without
editing the imported baseline sources. The passing invocation is bound to its
staged file hashes in `check/logs/staged-gate-final.json` outside the repository.

Source-only import reachability also passed for all five new modules from
both `InfoGeometry.All` and `InfoGeometry`, using the maintained import-coverage
implementation. This establishes routing, not successful compilation of the
complete umbrella dependency graph.

The tracked pre-commit hook invokes this same gate for the committing snapshot.

## Root-package integration boundary

The maintained source/provenance preflight
`python3 tools/infra/ci_bootstrap.py paths --root .` was observed to exit 1.
`InfoGeometryCore` is a materialized tracked tree. `Atlas` and
`HomotopyHypothesis` are required local path packages absent from the tracked
baseline, with no recorded gitlink, remote, or reproducible full pin. Their
absence is not caused by the sparse checkout. `GIFT` is separately a pinned
gitlink at `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` that is not initialized in
this checkout; this does not prove that its pinned source lacks a Lake file.

The narrow root build was actually attempted using the maintained
`run_locked_lake_build` entry point with `wfail=True` and the already-held
canonical build lock. It emitted:

```text
lake build --wfail InfoGeometry.Geometry.CourantDrinfeldDiracCapstone
fatal: write error: No space left on device
fatal: fetch-pack: invalid index-pack output
error: external command 'git' exited with code 128
```

Lake exited 1 while cloning Mathlib into the root package's dependency cache.
This invocation therefore did not reach owner compilation or establish a root
package result. The missing local-path packages described above are separate
findings from the source/provenance preflight; they were not the observed cause
of this invocation's failure. The tracked dependency configuration remained
unchanged. The already-provisioned exact-pin Mathlib checkout used by the
isolated verifier is separate from this failed root provisioning attempt.

A successful isolated source-closure check does not certify the root package or
the complete `InfoGeometry.All` dependency graph. No push-gate bypass or remote
publication is part of this receipt.

## Mathematical scope

The accepted targets are the native cotangent Lie structure and invariant
neutral pairing; the distinct hemi-semidirect left Leibniz operation and its
explicit matrix obstruction; algebraic KKS/unit-map identities; neutral graph
isotropy and equality with the orthogonal; the kernel intersection and exact
complementarity criterion; and their native finite-matrix coordinate adapter.

No smooth derivative identification, general Lie-bialgebra double, Courant
algebroid integrability, or entropy/Casimir identification is asserted.
