# Peirce derivation connection: accepted focused results

Disposition: **accepted limited scope**, 2026-11-22.

The new owner proves the Grassmann connection formula for an arbitrary Lie
action by noncommutative Leibniz derivations, using the existing native Peirce
submodule. For `p*p=p`, `rho = K.operatorAction`, and `s` satisfying `p*s=s`,

```text
nabla_x(s) = p * rho_x(s)
[nabla_x,nabla_y] - nabla_[x,y] = left multiplication by p*[rho_x(p),rho_y(p)]*p.
```

The action may be nonfaithful and may move `p`. The right-module Leibniz law,
actual derivative tangency, compressed-Gram curvature readout, fixed-projector
flatness, and compatibility with the existing integer-scalar inner connection
are proved. The direction-to-operator map is linear; it is not presumed to be
a Lie algebra homomorphism.

The owner contains **one definition and eight theorems**. All carriers,
projection operators, tangent interfaces, and curvature coefficients are
reused. No new axiom or theorem-bearing wrapper was introduced.

## Source and toolchain identity

- Base commit: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
- Lean: `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine focused Git dependencies match their corresponding root pins.
- Owner SHA-256: `ae651b99bb56edaebca105e673a1b08514a7991251adc2bda9246684b29b231f`.
- Audit SHA-256: `b0c2e8446cd0f5af7ff69f97bc30d3429ff8df8dd7f451304a1d2fe38adff1a7`.

Independent execution acceptance is preserved unchanged in
[QA_RECEIPT.json](QA_RECEIPT.json), SHA-256
`985e72c01c6f7eb1120be29f83d8d29d31d28f293593ec3d0c18c963bd81dde1`.
The separate mathematical review is preserved unchanged in
[SEMANTIC_REVIEW.md](SEMANTIC_REVIEW.md), SHA-256
`150db90bb8d9f4d15a227854588960c1bb4ea988fda67e0e2a6434ef2eb938fd`.
The receipt records the exact eight-path source snapshot before these reporting
files were added; all eight files were rechecked byte-for-byte during integration.

## Decisive checks

All **14 final QA commands exited 0**. Exact arguments, log hashes, input
hashes, dependency pins, and timings are recorded in the receipt.

| Check | Result |
| --- | --- |
| Focused explicit owner and audit build | Passed |
| Fresh owner and audit checks with `-DwarningAsError=true` | Passed, no new warnings |
| Public declaration coverage and axiom log | All 9 covered; each uses only `propext` and `Quot.sound` |
| Maintained compiled-module kernel/axiom replay | All 19 compiled declarations passed, including generated declarations |
| Strict OpenGauss screening | 0 traps |
| Strict placeholder screening | 0 hard findings; 2 reviewed soft assumption-group findings |
| Source axiom/debt audit | 0 gaps |
| Semantic-vacuity error gate | 0 errors; 1 reviewed definitional-evaluation warning |
| Semantic-content, authoritative-scope, and vacuity-linter gates | Passed |
| Actual staged proof-proxy gate | Passed |

The key reproducible commands are:

```bash
python3 verification/peirce-derivation-connection/audit.py
python3 verification/peirce-defect-boundaries/check.py build \
  InfoGeometry.OperatorAlgebra.PeirceDerivationConnection \
  InfoGeometry.OperatorAlgebra.PeirceDerivationConnectionAudit
python3 verification/peirce-defect-boundaries/check.py env lean \
  -DwarningAsError=true lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnection.lean
python3 verification/peirce-defect-boundaries/check.py env lean \
  -DwarningAsError=true lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnectionAudit.lean \
  > peirce-derivation-axioms.log 2>&1
python3 verification/peirce-derivation-connection/audit.py --log peirce-derivation-axioms.log
python3 verification/peirce-defect-boundaries/check.py env lean --run \
  tools/infra/axiom_check.lean \
  verification/peirce-defect-boundaries/.lake/build/lib/lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnection.olean
```

All compiler operations used the existing shared-lock wrapper. No existing
checker, wrapper, dependency declaration, or toolchain pin was changed.

## Reviewed findings and limits

The two soft placeholder findings identify explicit section assumptions:
algebraic carrier/scalar data and `IsLeibnizAction`. Neither assumes the target
curvature identity. The evaluation lemma `derivationConnection_apply` has an
intentional `rfl` proof of transparent map application; the substantive
curvature proof is separate. Independent semantic review accepted all three
findings without suppressions or checker exceptions.

The build replayed 65 warning headers from 29 pre-existing imported owners.
Both new files passed fresh checks with warnings treated as errors. The first
QA attempt also caught a new-validator bug: equality of the full root and
focused dependency sets incorrectly rejected the intended subset. That new
validator was repaired to check each focused pin against root, and the entire
final sequence then passed. The receipt retains the failure and repair hashes.

The semantic review includes the nonzero real matrix calculation
`p=E11`, `x=E12`, `y=E21`, giving curvature coefficient `-p` for the inner
action. This is an independent mathematical nonvacuity check, not an additional
Lean example theorem.

Focused acceptance covers the new owner and audit. The umbrella import was
reviewed statically and screened, but the full umbrella/root workspace is not
certified. Its external `HomotopyHypothesis`, `Atlas`, and `GIFT` reference
checkouts are unavailable in this environment. Publication-gate and remote CI
outcomes must be reported separately from these focused results.

The retained intake and contract distinguish ordinary derivations from
exterior differentials, pure-gauge flatness from projected curvature, mirror
involutions from square-minus-one real phases, and conditional positivity from
nilpotent-corner identities. This change establishes no additional physical,
octonionic, KMS, or analytic-limit identification.
