# Bilateral Peirce kernels: theorem and source contract

## Intake and reuse

This addition adapts `Pasted text(20261024-181215).txt`, headed
`TwoSidedCayleyDicksonLaplaceKernel.lean`. The reference source is main
`49f8b7681e76e6390fafaf993b3b26b968f4c629`. It reuses:

- `Core.DualSeedPeirce`: the actual four-equation seed predicate and the existing support/Majorana operators.
- `Core.PeirceRotor`: supported-block multiplication and the harmonic-completed rotor unit.
- `Algebra.AlternativeDerivations`: native `L_map` and `R_map` on the original carrier.
- `Algebra.ZornVectorMatrix`, `ZornDerivationBridge`, and `ZornAlternativeLaws`: the actual split-octonion product, its nonassociativity witness, flexibility and structural middle Moufang theorem.
- Mathlib's `HasDerivAt.mul`: the differential product rule in a normed associative real algebra.

No seed, inverse, projection, Vec3, octonion, or alternative-algebra predicate
is redefined. Finite matrices are witnesses, not replacement operator carriers.

## Source-derived algebra retained

For p=db, q=bd, Delta=p+q and D(l,m)=l p+m q, the action is
X |-> D(l,m) X D(r,s). It multiplies the four corners by lr, ls, mr, ms.
On the supported block a p+x d+y b+z q these are the exact four coefficients.
For lm=1, symmetric sandwiching fixes d,b and scales p,q; conjugate sandwiching
fixes p,q and scales d,b. The completed operators add 1-Delta and are ambient
units. The existing rotor is combined with these units in a specified order;
its inverse reverses that order.

## Explicit corrections and extensions to the intake

1. The four corner weights are **not independent**: (lr)(ms)=(ls)(mr).
   A concrete nonseparable four-weight assignment is refuted.
2. The sum of the four active corners is Delta X Delta, not an arbitrary X.
   A proper-support 3x3 example is annihilated by the active identity sandwich.
   The harmonic completion is used for ambient invertibility, not silently
   added to the active transform.
3. The general product D times rotor is ordered; the proved commutator is
   s(l-m)(d+b). No commuting exponential factorization or loxodromic
   classification is inferred.
4. The analytic module proves an actual `HasDerivAt` conclusion **conditional
   on the two factor ODEs and the signal derivative**. Opposite generator signs
   yield a commutator, equal signs an anticommutator. It does not identify the
   factors with exponentials or prove any differentiation-under-integral law.
5. The existing middle Moufang identity gives an equality of native linear
   endomorphisms and a finite-sum transport theorem. It does not give
   `(K X)(Y K)=K(X(Y K))`. The latter is explicitly refuted using native Zorn
   elements K=E11, X=V0, Y=V1. Distinct left/right maps have the associator as
   their exact commutation defect. Equal-kernel maps commute by flexibility.
6. A symmetric sandwich is not generally multiplicative, even with reciprocal
   invertible diagonal weights; this is checked on noncommuting matrix units.

## External primary-source comparison

S. V. Ludkovsky, arXiv:math/0612755v1, Section 3, Definition 1(4), PDF page 31,
defines “two-sided” by extending the integration interval to the whole real
line: F(f)=integral f(t) exp(-u(p,t;zeta)) dt. It is not a definition of a
left/right sandwich. Section 3, Theorem 13 (PDF page 33) requires a real-valued
second factor and convergence hypotheses for its convolution rule. The paper's
standard Cayley-Dickson tower is not an identification with the split Zorn
carrier used here. These statements were checked against the paper text;
web PDF screenshot rendering was unavailable during intake.

Primary source: https://arxiv.org/abs/math/0612755
PDF: https://arxiv.org/pdf/math/0612755

The algebraic sandwich construction is therefore retained as the attachment's
proposed construction, not attributed as Ludkovsky's definition or convolution
proof. No measure, integral transform, inversion, convergence strip, Mellin
change of variables, PDE diagonalization, analytic KMS structure, or continuum
limit is constructed by this addition. An associative `Ring` theorem is not
applied to the nonassociative Zorn product. Its endomorphism ring and original
carrier are kept distinct.

## Verification

The dedicated workflow compiles the unchanged repository import closure with
exact root Lean/Mathlib pins, under the shared sequential build lock. Every
declaration owned by the four new modules is audited in one imported
environment using public `Lean.collectAxioms`. Unsafe/partial declarations and
axioms outside propext, Classical.choice, Quot.sound are rejected.

Compilation and axiom audit are pending until a successful run is recorded in
the PR. No local compiler is available in the authoring environment. The
uploaded standalone source is not claimed to compile unchanged. This is a
scoped source-closure check, not a full root-Lake or All.lean build.

Production imports:

```lean
import InfoGeometry.Core.PeirceBilateralAction
import InfoGeometry.Analysis.BilateralGeneratorDerivative
import InfoGeometry.Algebra.ZornBilateralAction
```

Full-checkout test target, when root dependencies are available:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.TwoSidedKernelAudit
```
