# Matrix product-density repair contract

The `CuntzKMSState` normalized coefficient weights do not alone establish a
KMS functional on the full Cuntz algebra with its specified dynamics.
The next constructive step uses the existing full matrix-stage tower.

For a complex binary weight vector `q` with `q 0 + q 1 = 1`, define
`D 0 = 1` and `D (n+1) = reindex (D n ⊗ diagonal (2*q))`.
The factor 2 compensates for the normalized partial trace. Prove backward
partial-trace compatibility and normalized trace one at every stage.
These statements use no positivity assumption; positivity requires real
nonnegative weights and is a subsequent obligation.

Reuse `MatrixStagePartialTrace.normalizedPartialTraceStep_adjoint` and
`weightedStageFunctional_compatible_of_partialTraceCompatible` for descent.
Do not infer a full Cuntz KMS identity from matrix-core compatibility.

Owner search: `MatrixStagePartialTrace`, `CuntzMatrixCompatibleStateNet`,
`MatrixStageSelectedMatrixFamily`, and their consumers. The selected-stage
family extends with identity factors; the present recursion inserts a fresh
weight factor at every stage. Independent read-only search by Carson found
no such recursive weighted family in these owners and product-density searches.

Parent verification: `MatrixStageProductDensityAudit` passed, exit 0,
9352 jobs, log `/tmp/matrix-product-density-audit.log`. All three theorem
reports use exactly `propext`, `Classical.choice`, and `Quot.sound`.
The new modules emit no warnings; dependencies still emit warnings.
Independent source review by Poincare passed the normalization, reindexing,
backward compatibility orientation, and scope boundaries.

Independent QA passed: session 73062, exit 0, 9352 jobs;
`/tmp/matrix-product-density-qa.log`. Three axiom reports use only the standard
three axioms; zero own-source warnings and zero strict-screen traps.

Next contract: for real nonnegative q, identify the recursive matrix density
with its diagonal weights, prove native `Matrix.PosSemidef`, and apply
`FiniteMatrixGibbsFunctional.weightedTrace_nonneg` to every matrix observable.
With q0+q1=1, instantiate `CuntzMatrixCompatibleStateNet.weightedColimitFunctional`
using the existing backward-partial-trace compatibility theorem. Prove positivity
and normalization on this actual algebraic inductive-colimit carrier.
This does not assert norm completion or a full Cuntz KMS identity.
Parent audit now passes for the positivity/colimit additions (9354 jobs,
`/tmp/matrix-product-state-audit.log`). Thirteen declarations use only
`propext`, `Classical.choice`, and `Quot.sound`; no own-source warnings.
The implementation includes star preservation and `ComplexOrder` nonnegativity,
not just nonnegative real part. Matrix units evaluate to zero off diagonal
and to `2⁻ⁿ` times the recursive density weight on diagonal.
Independent semantic review passed. Distinct QA session 52895 passed with
exit 0 and 9354 jobs (`/tmp/matrix-product-state-qa.log`), 13 standard-axiom
reports, zero own-source warnings, and zero strict-screen traps.

The comments in `Algebra/CuntzKMSState.lean` now distinguish its actual
first-level normalized complex coefficient carrier from a positive state and
from the full word-diagonal algebra. No existing definition or theorem changed.
The new positive colimit functional is the constructive replacement for the
unsupported state interpretation. Full Cuntz KMS remains open.
