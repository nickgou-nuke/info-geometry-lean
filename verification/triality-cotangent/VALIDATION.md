# Validation record

## Final verified mathematical source

**Accepted for the algebraic scope in the theorem contract.** The dedicated
GitHub Actions run completed successfully, including the existing deep Cartan
consumer. This is focused kernel evidence, not a whole-repository certificate.

- PR: [#444](https://github.com/nickgou-nuke/info-geometry-lean/pull/444).
- Verified remote source head: `21816519e42b9f76a0c8004650c6b11a6024774f`.
- Matching local source head: `497c6d6664808e8ccb3082d6aabeba76dcd4e40a`.
- Exact shared source tree: `1c58b9eb55e126ebe8179702bdfec5e20bd73021`.
- Actual Actions merge: `508e1557896790de0eb4be072b27bf2501070745`, with
  base `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
- [Run 45385261804](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45385261804),
  [job 138414407353](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45385261804/job/138414407353):
  **success**, 2026-11-24.
- Lean `4.34.1`, revision `5045d0056413266e57c625dcd7c365b10e377c52`;
  Lake `5.0.0-src+5045d00`; Mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine dependency pins
  match the root package. No pin or toolchain change was made.

| Check | Actual result |
|---|---|
| Seven mathematical owners and audit-module build | Lake exit 0; 3,298 jobs including dependencies |
| Separate fresh `env lean` invocation of the audit module | Exit 0 |
| Explicit declaration/axiom coverage | All 202 declared public names, each exactly once |
| Foundational dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Strict OpenGauss screen on seven owners plus audit | Exit 0; zero findings |
| Existing `KreinCl44SplitG2DerivationPosetSynthesis` consumer | Lake exit 0; 9,048 jobs including dependencies |
| Source/configuration/runtime before/after stability | Passed for build, fresh audit, and regression |
| Installed staged proof gate on source commits | Passed |
| Whole repository and root pre-push certificate | Not claimed; see separate existing CI blockers |

The actual fresh audit artifact was downloaded and parsed independently;
no combined build log, synthetic output, or timestamp-normalized substitute
was used. The parent independently ran the same validator on the raw artifact
and obtained exit 0. The mathematical source review and independent QA record
are in [reviews/source-review.md](reviews/source-review.md) and
[reviews/final-validation-review.md](reviews/final-validation-review.md).
Historical failed checkpoints remain below and in the other review files.

The native build emitted six unique nonblocking style warnings in the new
owners: two unnecessary tactic sequencing warnings, three unused section
variable warnings, and one unused simp argument. They were not suppressed.
The raw regression log additionally contains warnings from existing owners.
No Lean error record occurs in the successful job. A zero-trap strict source
screen is not described as a warning-free Lean build.

### Reproducible commands

Executed with the unchanged focused package and pinned runtime:

```bash
set -euo pipefail
python3 verification/triality-cotangent/audit.py
python3 verification/triality-cotangent/check.py build
python3 verification/triality-cotangent/check.py env lean lean/InfoGeometry/Geometry/TrialityCotangentAudit.lean 2>&1 | tee triality-cotangent-axioms.log
python3 verification/triality-cotangent/audit.py --log triality-cotangent-axioms.log
python3 verification/triality-cotangent/check.py build InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
```

The workflow captures the build and fresh Lean outputs with `tee` under
`set -euo pipefail`. Its strict source-screen command is recorded verbatim in
[the workflow](../../.github/workflows/triality-cotangent.yml). Local native
requests remained behind another task's maintained shared lock and were
cancelled only while waiting, before starting Lean/Lake. No competing compiler
was stopped, and no local native-build success is claimed.

### Preserved execution evidence

Actions artifact `14916487441`, `triality-cotangent-validation`, contains the
three raw logs. Its ZIP SHA-256 was verified before extraction:
`e5cf4cfe9ac3812b57bc21fe148be32dadb6a074a09229a506810bd541fa87fa`.

| Raw file | Bytes | SHA-256 |
|---|---:|---|
| `triality-cotangent-build.log` | 42,794 | `103c99578b06cffa540a6742573e27f524e23bc29e222e76ab53e3eccae7750a` |
| `triality-cotangent-axioms.log` | 24,873 | `bb5a2be5a44178a5216cd9fb53e9a32ddbdf446c600e5a0c0e8297a6e8f1c084` |
| `triality-cotangent-regression.log` | 309,207 | `4081cf2437614089d755004bc3b6455b6a3b07b178ae3a8590ed14d72ceab698` |

The focused build and fresh audit share the 53-file source/configuration
snapshot `be56d8ec0eec0d8f3fcb2520cf95ca6459e5fbd5d1039f9e6039b0da335cc75d`.
The regression's 175-file snapshot is
`cc2715c1a00fc7455ab78f25d1b154b1ebcde43600c7a45915c58ebd8e371885`.
Counts include the recorded package and validation controls, not only Lean
owner files. All before/after comparisons passed.

The publication checkpoint adds only validation documentation and review
records after this verified source commit. The Lean sources, package pins,
verification scripts, and workflow are unchanged. The successful run above
is named explicitly; a later documentation-triggered run is not represented
as already completed.

### Remaining scope

The exact algebraic claims and the shear countermodel are proved. Smooth
cotangent-bundle construction, closedness and multiplicativity of a
symplectic differential form, an actual Killing-form normalization, and
integration to outer `Spin(4,4)` / fixed `G₂(2)` geometry remain separate
mathematical obligations. Existing failures of other repository workflows are
classified with actual logs and unchanged-path comparisons in
[reviews/existing-ci-blockers.md](reviews/existing-ci-blockers.md).

## Initial candidate checkpoint

- Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529` (`main`).
- Lean pin: `leanprover/lean4:v4.34.1`.
- Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Canonical sources are pending kernel validation at this checkpoint.
- The initial local check waited for the maintained shared build lock, held
  by another task. The waiting request was cancelled before acquiring the
  lock or starting Lean/Lake; no competing compiler process was stopped.
- The dedicated GitHub workflow is the remote kernel-validation route.
- A mathematical challenger independently checked the groupoid semantics,
  Reynolds dual equivalence, shear counterexample, coordinate conjugacy and
  faithful finite action. Its review is not a compilation result.
- The extracted Cartan declaration block is byte-for-byte equal to the
  original block; the existing consumer is a separate regression target.

## Initial kernel run and repair

- PR: [#444](https://github.com/nickgou-nuke/info-geometry-lean/pull/444).
- Initial remote head: `501523dba3ec6e433e1d63b30b47f0cf9172099b`.
- [Run 45370890807](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45370890807),
  job `138364561788`, failed during the focused owner build. It reported 27
  error records in three introduced owners. No successful kernel or axiom
  result is inferred from that run.
- The real Lie section had competing additive/module structures. The generic
  linear and native Lie sections now have separate instance scopes, also in
  the finite-invariant owner.
- Native groupoid instances now use explicit `ActionCategory` structures;
  transport proofs use fully instantiated equalities. The Cartan proofs now
  expose the relevant coordinates before arithmetic.
- The four-owner repair is local commit
  `40524ac6ac26db06a1c215c80854a42adf1645e7`, remote commit
  `a117cc7c721e7ddae997108b94c707ebb91da00b`, exact shared tree
  `6f7837dba9845c2b00b2aec9992059eeaa416146`.
- Source inventory: 202 explicitly named public declarations across seven
  owners. Strict OpenGauss screen: zero findings. The installed staged proof
  gate passed. These are source checks, not kernel validation.
- The independent mathematical re-review found no new hypotheses, weakened
  conclusions, changed carriers or signs, or proof bypasses.
- The repaired [run 45372287199](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45372287199)
  built `CotangentLieForm`, `FiniteCotangentInvariants`, and `CartanTriality`.
  It then failed with 16 error records in the other three directly tested
  owners. The downstream Cartan cotangent specialization and fresh audit
  were not established by that run.

## Second repair checkpoint

- The remaining groupoid reconstruction now passes its actual action to the
  native object equivalence explicitly.
- The shear counterexample now uses explicit linearity and bilinear-map
  extensionality; theorem statements are unchanged.
- The faithful representation proofs reduce concrete `ZMod.val` exponents
  before expanding matrix entries. The preceding errors left those exponents
  opaque; no false numerical identity was detected.
- Local commit: `1f25de0af0a511911fc916bc95ab6cfa30ff7265`.
- Remote commit: `bb97742c13502115bfb4a5e93bfb5c8602417542`.
- Exact shared tree: `5624c120b6f20beb2789391ca5d20ae04d81ce75`.
- Inventory remains 202; strict source screen and installed staged gate pass.
- [Run 45374651357](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45374651357)
  built all five foundational owners. Only `CartanTrialityRepresentation`
  still failed: modular exponents remained opaque, the entrywise proof
  reached its heartbeat limit, and a multi-location arithmetic tactic tried
  to continue after closing a contradiction.

## Symbolic representation repair

- Matrix multiplication now follows the existing order-three/reflection
  presentation. Rotations use `ZMod.val_add` and `pow_mod_orderOf`; three
  residue cases give the reflection interchange law. Four symbolic products
  establish the native dihedral homomorphism.
- There is no matrix-entry enumeration in this multiplication proof and its
  former two-million-heartbeat override is removed. The faithful matrix
  representation and all public statements are unchanged.
- Local commit: `0552cb77f230a6122b93c3716a0edec1a7af79e2`.
- Remote commit: `f9941cfcf0f6e301dc5d91fd536ddc03e0a31776`.
- Exact shared tree: `5dd098208cc57e2a9922988d38a7f2e74d0b42b0`.
- The mathematical challenger and a second source reviewer independently
  checked the multiplication order and native Mathlib formulas.
- [Run 45377750385](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45377750385)
  compiled the six prerequisite owners, including the faithful symbolic
  representation in 11 seconds. The only remaining failure was typeclass
  synthesis for `Module.Free ℝ cartanRepresentation.dual.invariants` in the
  final four-dimensional finrank proof. The fresh axiom invocation and
  existing-consumer regression were not run.

## Import check and direct finite-basis repair

- Adding the native vector-space basis import did not resolve the synthesis
  obligation. [Run 45382587201](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45382587201)
  at remote head `35459c0d4f933e9b78ba3bd9860abcfc58d7e3a3` again built six
  owners and failed only at the same final dimension theorem. This failed
  attempt is recorded rather than counted as validation.
- The final dimension proof now constructs a native basis indexed by
  `Fin 2 ⊕ Fin 2`. It takes the product of the proved fixed Cartan basis and
  its native dual basis, then transports that basis through
  `fixedCartanCotangentEquiv.symm`. `Module.finrank_eq_card_basis` gives four
  directly. No additional hypothesis or replacement carrier is introduced.
- Local commit: `497c6d6664808e8ccb3082d6aabeba76dcd4e40a`.
- Remote commit: `21816519e42b9f76a0c8004650c6b11a6024774f`.
- Exact shared tree: `1c58b9eb55e126ebe8179702bdfec5e20bd73021`.
- `CartanTrialityCotangent.lean` SHA-256:
  `5e411f959b1f150b65e4b2d3640e89f3dca831777b8d4e046ad0b664f848411d`.
- Source coverage is still 202 declarations across seven owners. Strict
  OpenGauss screening and the installed staged proof gate pass.
- [Run 45385261804](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45385261804)
  completed successfully, including the existing-consumer regression. The
  independent raw-artifact audit and final execution details appear above.
- The final local request was cancelled while still waiting for the shared
  build lock, before starting Lean/Lake. The successful kernel evidence is
  the dedicated CI execution; no local build success is claimed.

The final verified source and exact execution evidence are recorded at the
start of this document. Earlier failures are historical checkpoints only.
