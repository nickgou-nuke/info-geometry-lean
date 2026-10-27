# Twisting Twistor space: theorem contract

Source: Tim Meier and Eggon Viana, *Twisting Twistor space*, arXiv:2601.19983v1,
27 January 2026, attached 44-page version. This addition is based on main
b143075bbf27e75860a1011e04423a0f227b7c41. It changes no existing owner, dependency
pin, root import, prior PR branch, or external reference checkout.

## Source-to-code coverage

- (2.2)--(2.5), (4.4): paper coordinates (lambda,mu) with mu=x lambda reuse
  PenroseIncidence's Spinor2, Twistor4, ComplexSpacetime and native Projectivization.
  The existing convention is (i x lambda,lambda). An explicit native linear
  equivalence relates the conventions. The Euclidean hat operation is antilinear,
  squares to -1, and a nonzero spinor gives an invertible two-column frame.
  Frame reconstruction proves incidence and uniqueness with the hatted incidence.
  Projective zero vectors and zero scaling are not admitted.
- (3.3), (3.5): TwistCoproduct uses native Bialgebra, algebraic TensorProduct and
  Units. Conjugation of comultiplication is an AlgHom. R=F_op F^-1 satisfies
  R_op R=R R_op=1. These facts do not establish coassociativity or Yang--Baxter
  for an arbitrary unit; those require the extra cocycle.
- (3.1)--(3.5): RepresentedTwistProduct records the two-/three-tensor inverse
  twist actions, module-algebra naturality, normalization and inverse cocycle.
  It derives associative unital multiplication, a conjugated involutive flip,
  braided commutativity when the initial algebra is commutative, and differential
  Leibniz when the differential tensor action commutes with the twist. It does
  not assume associativity as a field. A full universal-enveloping action adapter
  and formal-power-series completion remain separate obligations.
- (3.4), (3.6), (4.2)--(4.3): FirstOrderTwist constructs an actual associative
  noncommutative coefficient Ring on A plus h A with h^2=0. This is exact modulo
  h^2, NOT an asserted all-orders star product. Its Hochschild cocycle comes from
  native Derivation objects. The concrete polynomial example uses lambda0 d_mu0
  and lambda0 d_lambda1, Poincare vector fields in (2.9), and proves they commute.
  Fibre coordinates commute with each other while the mixed commutator is
  h lambda0^2 and nonzero. The example is our specialization of the paper's
  construction, not an example explicitly worked out in the text.
- (3.8), (3.31)--(3.32): compatible differentials lift unchanged to the jet
  algebra. TwistedGaugeCoefficients constructs the existing OperatorValuedConnection
  from actual additive Leibniz maps, derives infinitesimal curvature covariance
  and the differential Bianchi identity, and instantiates covariance on the
  constructed polynomial deformation.
- (4.19)--(4.21): cyclic additive functionals and a central volume coefficient
  imply vanishing of the BF coefficient variation. Cyclicity is a hypothesis;
  no functional is identified with an actual twistor integral here.

## Source convention issues: no silent repair

Equation (3.31) prints delta A=-d epsilon+[epsilon,A], whereas (2.21) and (4.18)
print a plus sign on the differential with the same written commutator order.
Using F_ij=d_i a_j-d_j a_i+[a_i,a_j], the minus convention gives
variation F=[epsilon,F]. Holding these definitions fixed, the plus convention
has residual 2([d_i epsilon,a_j]-[d_j epsilon,a_i]). Both formulas and a
nonzero matrix example are included; the plus-sign covariance is not asserted.

Equation (3.8) uses the degree of the left form in the graded Leibniz sign;
(4.13) prints the degree of the right form. This PR implements the coefficient
(degree-zero) differential calculus, not a resolution of that graded discrepancy.

## Not yet implemented by this PR

The full Poincare enveloping Hopf action, cocycle-to-coassociativity adapter,
all-orders twist exponential and quantum Yang--Baxter theorem; twist
unimodularity and integration cyclicity construction; global complex manifolds,
holomorphic bundles, Dolbeault cohomology, CP1 fibre integration (2.18),
gauge fixing, nonlocal action, Penrose transform equivalence, supertwistor
Berezin integration, supersymmetric Chern--Simons action, and the full
BF/Yang--Mills or N=4 SYM equivalence are not proved here. No finite matrix toy
is substituted for these missing constructions.

## Acceptance

Pending until the exact source closure compiles and every declaration owned by
all seven new modules passes the transitive axiom audit. The scoped workflow is
not a full repository build. No custom axioms, admitted proofs, native_decide,
unsafe declarations or dependency stripping are allowed. The PR records actual
revision, run and audit results; source declarations alone are not acceptance.

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Twistor.TwistingTwistorAudit
```
