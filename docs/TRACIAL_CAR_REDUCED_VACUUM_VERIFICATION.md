# Weighted CAR functionals and finite reduced vacuum

The owner modules are `OperatorAlgebra/TracialCARDensity.lean` and
`OperatorAlgebra/FinitePairingReducedVacuum.lean`.

## Mathematical scope

The first reuses `NCG.TracialFunctional`, native units, and `SplitClifford.CARPair`.
It proves weighted-trace covariance, density/adjugate products, division-free
boundary identities, sector readouts, and the ordered vacuum excitation identity.
For annihilation `b`, the vacuum support is `bB`, whereas `Bb` is occupation.
For `rho = a Bb + c bB`, the occupation readout has weight `a` and the vacuum
readout has weight `c`. No positivity or normalization is inferred for a generic
tracial linear functional.

The second specializes the existing finite pairing rotor to the existing
product-index complex matrix carrier and computes its ordinary partial trace.
For real coefficients `c,s`, the global amplitude is `c|00> - s|11>` and the
reduced density is `c^2 (a A) + s^2 (A a)`. It proves positivity via an actual
Gram factor, trace, purity, and both unitary identities under `c^2+s^2=1`.
Reduced purity is strictly below one exactly when `c*s != 0` under normalization.
The coherence sign and the absence of a normalized-partial-trace factor are
explicitly checked in the matrix entries.

These are algebraic boundary identities and finite matrix theorems. They do not
assert an analytic KMS strip condition, a general GNS completion, thermal
interpretation, or positivity preservation by arbitrary nonunitary similarities.

## Verification evidence

- `TracialCARDensity`: committed as `58428da29`; locked owner build and all
  34 declarations passed the axiom audit. Rechecked during the v3 candidate run.
- Reduced-vacuum v3 failed only at a reversed scalar sum; its warning was also
  removed. No theorem conclusions were weakened.
- Scratch v4: `/tmp/qa-reduced-v4-resume/result.json`, compile and all 28
  declarations passed, stable source/import/pin hashes. No owner-scoped warnings;
  dependency-local-change warnings were reported for LeanCopilot and LeanArchitect.
- Live promotion changes only the scratch-status documentation. Aggregate import
  build `+InfoGeometry.OperatorAlgebra.All:olean` and the live 28-declaration
  axiom audit passed in `/tmp/qa-reduced-live-resume/result.json`, with stable
  captured source/import/pin hashes.

No unrelated submodule edits or dependency pin changes are part of this work.

## Independent final review

Popper independently reviewed the final delta and returned source A-A PASS.
The v2-to-v4 changes comprise proof normalization, explicit complex-order scope,
and lint cleanup; v4-to-owner changes only promotion documentation.
No hypotheses or conclusions were weakened.

Ampere independently reran both live owner targets and the operator-algebra
aggregate, then audited all 28 reduced-vacuum and 34 tracial declarations.
Receipt: `/tmp/qa-a-reduced-live-final-qwij16ml/result.json`, all commands exit
zero and captured sources/pins stable. This completed run preceded the later
finite-bilinear addition to `KitaevChainMajoranaZeroModes`; it does not certify
that later aggregate state.

Reviewed owner SHA-256 values:

- Reduced vacuum: `4b952dbf74ce7f1d87e60ea456f580d7f3c72eeb5b9977dc9257f82231a6be2f`
- Tracial CAR: `3250e08ddd6375cf8989ebebe0f69a11d78802e89ede16841e1835b4350dfa53`

## Density-defect extension

Seven separate lemmas were added directly to `TracialCARDensity`:
`weighted_commutator_defect`, the four density commutator/anticommutator
identities for the explicit sum/difference Majorana combinations,
`two_smul_density`, and `annihilator_commutator_boundary`.
They reuse the native weighted linear map, density eigenproducts, and chirality.
No division by two, positivity, normalized state, or analytic KMS assumption
is introduced. In particular the commutator coefficient is `c-a`, while the
anticommutator coefficient is `a+c`.

Kepler drafted the sandbox candidate; Popper returned source A-A PASS for both
the seven-lemma candidate and its unchanged promotion into the owner. Parent
executed the prepared scratch check (seven declarations clean). Ampere then
independently executed the decisive live check with default permissions:

- `lake build +InfoGeometry.OperatorAlgebra.TracialCARDensity:olean +InfoGeometry.OperatorAlgebra.All:olean`: PASS, 9979 jobs.
- Full owner axiom replay: **41 declarations clean**, standard allowlist only.
- Zero owner-scoped warnings/errors; existing dependency/aggregate warnings remain.
- Captured owner, aggregate, Kitaev dependency, scratch and pin hashes stable.

Receipt: `/tmp/qa-tracial-defects-live/result.json`, session 12233, exit zero.
Updated owner SHA-256:
`6734a0e8dfeca118bfded0a477c4bc85873bee401db8ab1e3a70c3b31124af16`.
The earlier 34-declaration count/hash is historical and superseded for this owner.

## Algebraic vacuum covariance and observable expectations

The next owner extension adds three separate lemmas:

- `GNSAction.RepresentationState.act_vacuum_eq_zero_iff_null` characterizes
  annihilation of the cyclic vacuum by membership in the native state null set.
- `pullback_act_vacuum_eq_zero_iff` transports that condition along the existing
  star-preserving real algebra equivalence and state pullback. This uses the
  existing algebraic quotient, with zero written as its explicit quotient class.
- `FinitePairingReducedVacuum.firstFactor_expectation` evaluates any complex
  first-factor observable `X` on the actual rotated vacuum as
  `c² * X 0 0 + s² * X 1 1`. It reuses the ordinary partial-trace trace duality
  and native reduced-vacuum theorem; normalization is not required.

The matrix-only annihilator theorem and specialized zero wrapper were removed
from `AttentionGNSBridge`. Both attention consumers now use the generic owner
lemma and explicit quotient zero. Its audit declaration references were updated accordingly.
No replacement state, quotient, or representation carrier was introduced.
These results do not construct covariance of completed complex GNS Hilbert
spaces or prove an analytic KMS boundary condition.

Kepler authored the GNS sandbox candidate; James authored the expectation
candidate. Popper independently returned source A-A PASS for both candidates
and all four promoted files. Ampere independently checked the candidates and
then reran the final live checks under the shared build lock:

- Four-file owner/audit build: PASS, 9380 jobs.
- `InfoGeometry.OperatorAlgebra.All:olean`: PASS, 9979 jobs.
- All-declaration axiom replay: 87 clean (GNSAction 33, ReducedVacuum 29,
  AttentionGNSBridge 25); the audit file adds no declarations.
- Nine audit axiom prints contain only standard foundational axioms.
- Zero scoped warnings/errors; upstream/package warnings remain.
- Captured owner, aggregate and dependency-pin hashes stayed stable.

Receipt: `/tmp/qa-a-gns-expectation-live-m00bzbs5/result.json`, session 69854,
terminal exit zero. Final owner SHA-256:

- GNSAction: `0ab08d9d741a26faaf0a99c2857f2541d2da5344e7dacda402d7995b96b99ee8`
- ReducedVacuum: `d77242d49b4baf25f8417c27c4fc3546feb4be692ef9a0493dffb14754069b79`
- AttentionGNSBridge: `cda35dfef7017ba60f276520b0c6702b27e4645e519f5149555827b2fd74660b`
- AttentionGNSBridgeAudit: `4b60e88c305ff668b32abdbced98124436ed0b047dccc9c8c3ee05a7c52fedde`

This is scoped acceptance. Concurrent unrelated work and the whole-repository
release gate remain outside this receipt.
