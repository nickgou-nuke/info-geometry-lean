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
