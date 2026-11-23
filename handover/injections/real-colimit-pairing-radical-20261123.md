# Real direct-limit pairing and radical continuation — 2026-11-23

## Publication scope

Branch: `codex/real-colimit-pairing-radical-20261123`.
Target: PR #432 branch `codex/zeta-weil-krein-stokes-20261123`, remote base
`c40e82ff31a4d5eb17aac53c63f3facbe0cd1ded`.
The local base `be2eaf5109f90b6fbcf55f7156ebeebedaa08f75` has the exact same
reviewed tree `82567210b8c8cc74372da8bb5bb0213b2bc28e61`.

This is a draft source checkpoint. No Lean kernel acceptance, executed axiom
certification, full root build, or successful root publication gate is claimed.

The theorem contract is `docs/REAL_DIRECT_LIMIT_PAIRING_CONTRACT.md`.
The verbatim user proposal and its digest are under
`docs/intake/real-colimit-20261123/`.

## Changed mathematical owners

- `LinearAlgebra/DirectLimitBilinear`: actual native form, uniqueness, positivity
  equivalence and survival of negative witnesses.
- `LinearAlgebra/DirectLimitEndomorphism`: actual native operators, involution,
  square-zero, reflection, commutation and eigen-equation transport.
- `LinearAlgebra/DirectLimitReflection`: consumes existing reflection theorems,
  with an explicit nonzero-image premise for a native eigenvector.
- `LinearAlgebra/DirectLimitPairingOperators`: stage adjoint pairs imply radical
  preservation and construct a native quotient operator.
- `LinearAlgebra/DirectLimitRadicalQuotient`: persistent-radical characterization,
  symmetric-PSD stability, a counterexample for the indefinite case, and the
  native linear equivalence under radical stability.
- `Modular/NativeDirectLimitDerivation`: realizes the existing derivation
  interface on the native algebraic limit and transports the finite remainder.
- `Arithmetic/FiniteEulerLogDerivative`: two unit logarithmic-derivative
  naturality lemmas.
- `Clifford/RealFockInfinityPairing`: identifies the existing pairing with the
  generic form on its existing carrier.

The eight-owner inventory includes 80 explicitly named public declarations,
including existing declarations in modified owners. This is not a count of 80
new theorems or a whole-environment enumeration.

## Executed author validation

```bash
export PATH=/workspace/scratch/5c48dfbb2253/validation-runtime/lean-4.34.1-linux/bin:$PATH
python3 verification/real-colimit/check.py --output-dir artifacts/verification/real-colimit-author
```

Result: exit **2**, status `source_checks_passed_kernel_blocked`.

- Exact focused dependency pins and toolchain: passed.
- Source inventory and forbidden proof construct check: passed.
- Strict OpenGauss screener and refutation screen: passed, zero traps.
- Static GATE_4: passed with explicit kernel-unverified status for all eight owners.
- Semantic-vacuity screen: zero errors and eight reviewed warnings. These are
  representative/coordinate computation lemmas, not assumed positivity or a
  supplied universal property.
- Selected-source hashes remained unchanged during source checks.
- The actual nonblocking shared-lock probe failed because owner
  `real-matrix-split:6` retained `/tmp/info-geometry-build.lock`.
- No compiler command started, and no lock was bypassed or removed.

The first source screen flagged `ring` within the explicit hyperbolic form's
scalar coordinate proofs as an operator tactic. The same statements were
rewritten with full scalar equalities, distributivity/associativity and additive
rearrangement. The rerun above is clean. No gate was changed or suppressed.

The generated compiler plan, not yet executed, builds all eight owners plus the
existing `RealFockHilbertCompletion` and `ZetaDihedralWeilKreinAudit` targets with
warnings treated as errors, then checks fresh sources and `#print axioms`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by that audit.

## Independent review

- G-A: root, `universal_identities`, and `zorn_realization`; workers wrote isolated
  candidates and root reviewed/integrated them.
- A-A: `paper_audit`; mathematical source review passed, with three documentation
  clarifications applied (arbitrary stages, one finite power cutoff, and symmetric
  PSD target forms). Final integrated source, contract, verifier, and workflow
  review: **PASS at source/mathematical scope**, with no outstanding correction.
  No compiler or tests were run by the audit agent.
- QA-A: `acceptance_qa`; **source-ready draft; kernel acceptance blocked**.
  The independent full-verifier run used the same pinned toolchain and
  `--output-dir artifacts/verification/real-colimit-qa`, returning exit 2 with
  the same occupied-lock status, 80-declaration inventory, and owner hashes.
  No source correction remains. This is not acceptance of the Lean proofs.
- The independent scoped staged proof gate, intake digest verification,
  `git diff --cached --check`, and `git diff --check` all exited 0.
  The eight staged Lean blobs match the checked source hashes; the intake,
  digest, contract, workflow, verifier, and README match their staged copies.
- The generated worker parses and its exact ten-command plan matches the
  report. No executed compiler receipt exists. Compiler QA and the separate
  root publication gate remain outstanding.
- Publication must preserve this source-reviewed, kernel-unverified draft
  status. The remote tree is compared with the final local committed tree
  before the PR is opened.

## Source snapshot

| Owner | SHA-256 |
|---|---|
| `lean/InfoGeometry/LinearAlgebra/DirectLimitBilinear.lean` | `e7a6112efe72b1ea841a570b6b3232e63191b5bce2969cdee110d07a21ca090d` |
| `lean/InfoGeometry/LinearAlgebra/DirectLimitEndomorphism.lean` | `bc3774c5d2bc996c615d69395baec8f7fe0a2dd4c5527927e43aca23c8d5cf9a` |
| `lean/InfoGeometry/LinearAlgebra/DirectLimitPairingOperators.lean` | `3d210a23aec0a1ee1b2d5b622f0b1e049f95399cb6e6c7a192e2c38d254b6fe7` |
| `lean/InfoGeometry/LinearAlgebra/DirectLimitRadicalQuotient.lean` | `aaadd0890c5494c1d0c20d223906257944d9c9b102aa7b94d6dea75d1f21ebf6` |
| `lean/InfoGeometry/LinearAlgebra/DirectLimitReflection.lean` | `04b71f4b9fcc00101d2ac02aa54c3acc675e4eb0b06d6e2b7c0779ad3b5352e2` |
| `lean/InfoGeometry/Arithmetic/FiniteEulerLogDerivative.lean` | `0dcda9b5b15589370b3bcd81220208af3714f5f21914a7bc903a04bb075aad5d` |
| `lean/InfoGeometry/Modular/NativeDirectLimitDerivation.lean` | `a11c9d1fb59e65ff451be10c19562b5708a86155832ce452c8a5703f821f084c` |
| `lean/InfoGeometry/Clifford/RealFockInfinityPairing.lean` | `a34b2502da5eac1aa08f9366699e4d6b1d3cfe9ba2a793413b2a79a3a42d1e94` |
