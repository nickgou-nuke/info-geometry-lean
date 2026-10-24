# Division-free Cartan/Drazin-MP synthesis

## Intake and source contract

Source: `Pasted text(20261023-181411).txt`, the seven-stage nilpotent,
idempotent, star-projection, reflection, Peirce, Drazin/MP and anomaly note.
Inspected base: `21189e55133ed207043f2f05e37aa52d1fc8a9f5`.

The requested ladder is retained, with inverse witnesses and characteristic
conditions explicit. This is an additive adaptation, not a claim that the
standalone input compiles unchanged. Existing owners and dependency pins are
not edited.

Actual carriers: arbitrary associative unital rings, then star rings where
Penrose supports or adjoints are used. Exact matrix instances use native
`Matrix (Fin 2) (Fin 2) R` over the reals and `ZMod 2`.

## Existing owners reused

- `Core.PeirceDecomposition`: complement, four components, decomposition,
  and zero-product corner routing.
- `Canonical.Drazin`: the native Drazin predicate, projection and complementary
  projection, their commutation, and the Fitting nilpotent power theorem.
- `Singular.MoorePenrose`, `MoorePenroseSectors`, `SquareZeroMoorePenrose`:
  native Penrose predicate, star projections, and dual square-zero theorem.
- `Singular.MetricAlgebraicProjectionDefect`: the actual commutator-defect
  definition and the metric-first projection-defect sign convention.

`Cartan.Involution` was also inspected: its endomorphism eigenspace projectors
start with an invertible scalar two. This addition instead starts from the
existing arbitrary-ring Peirce components and does not replace that owner.

## The seven stages

1. Supplied reflexive equations yield native `IsIdempotentElem` supports;
   square-zero yields the first ordered support product equal to zero.
2. Supplied native Penrose equations upgrade the supports to `IsStarProjection`.
   The existing star argument supplies reverse orthogonality and dual nilpotency.
3. An idempotent p gives g = 2*p - 1 with g*g = 1; a star-fixed p gives star g = g.
4. E_p(x) is the sum of the 11 and 00 components; O_p(x) is the sum of the
   10 and 01 components. They are complementary additive projections with
   unique decomposition and the two-piece multiplication rules. Conjugation
   by g is bundled as an actual `RingEquiv`.
5. x + g*x*g = 2 E_p(x), x - g*x*g = 2 O_p(x), and
   O_p(x) = g*(p*x-x*p) = p*(p*x-x*p)-(p*x-x*p)*p.
6. For a native Drazin witness, p=a*d is idempotent; a, d, p and the Fitting
   nilpotent summand are even. The power bound is k+1, valid also at k=0;
   the supplied witness exponent is not asserted minimal.
7. Relative to p, the two spectral-first anomalies against a*m and m*a are
   odd and recover the odd parts of the metric supports. Their signed
   difference controls the commutator with m*a-a*m. Directed corners return
   to square-zero. A new MP ladder requires a supplied inverse of that corner.

The generic anomaly identities only require the Drazin witness and an arbitrary
m. The master theorem additionally takes the native MP witness so its
"metric supports" really are self-adjoint projections.

## Explicit boundaries and corrections to the intake

- A star ring alone does not provide generalized inverses. They are hypotheses.
  The construction is a dependency ladder with a reusable feedback step, not
  an unconditional existence cycle or an antisymmetric poset with a cycle.
- The arbitrary-ring Peirce split does not require division by two. Recovering
  its components from reflection sign eigenspaces requires injective doubling.
  The exact ZMod 2 matrix example has g=1 but a nonzero off-diagonal component.
- The two directed off-diagonal corners are square-zero. Their sum need not be:
  the real swap-matrix example is odd and squares to the identity.
- For an arbitrary MP pair, m*a-a*m is self-adjoint, not automatically
  tripotent or involutive. The oblique 2x2 example proves failure of tripotence.
- "Cartan" here refers to the algebraic two-block parity. No positive Cartan
  involution on a semisimple Lie algebra, symmetric space or metric existence
  theorem is asserted.
- The intake uses [spectral,metric]. The existing projectionDefect uses
  [metric,spectral]. `leftAnomaly_eq_neg_projectionDefect` records the sign.
- The intake's call `projector_to_involution hPD hPD hPD rfl rfl` does not
  supply the required orthogonality between repeated copies of a nonzero
  idempotent. The standalone reflection-square lemma avoids that invalid call.
- No theorem is added claiming the reflection is self-adjoint for an oblique
  Drazin projector, or that projection mismatch is a physical anomaly.

## Verification

The dedicated workflow reads the exact root Lean and Mathlib pins, copies the
full unchanged repository import closure, compiles sequentially under the
shared lock, and uses public `Lean.collectAxioms` to audit all declarations
owned by the three new modules. It rejects unsafe/partial declarations and
axioms outside propext, Classical.choice, Quot.sound. There are no exemptions.
Its report and compiler logs, rather than this source document, establish the
current acceptance status. This is not a full root-Lake or all-green-CI claim.

In a full checkout with root dependencies available:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.CartanDrazinMPExamples
```

Production import:

```lean
import InfoGeometry.Canonical.DrazinMPCartan
```
