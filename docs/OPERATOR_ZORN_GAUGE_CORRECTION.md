# Operator-Zorn gauge correction to PR #146

## Carrier and scope

The field algebra is the existing nonassociative operator-Zorn carrier,
`InfoGeometry.Canonical.OperatorZornMatrix A`, definitionally the existing
`InfoGeometry.Physics.NCG.NCZornElement A`. Its multiplication remains
`NCZornElement.mul`. No `Ring` or alternative-algebra instance is installed
on this carrier, no associative quotient is taken, and no matrix/Clifford
representation replaces it. `[Ring A]` concerns the coefficient operator
algebra only.

The native real split-octonion owner `ZornVectorMatrix R` and its circular
Peirce frame remain separate from the operator-coefficient lift. In
particular, scalar-coefficient alternativity is not imported into the
noncommutative coefficient lift. `NCZornAlternativityAudit` already supplies
explicit failures of that extension.

The earlier CAR/Clifford modules in PR #146 are separate representation
results. They do not implement the full four-potential gauge problem and
are not the primary field carrier for this correction. No source is deleted.

The connection coefficients are now indexed by an arbitrary type `Direction`,
via `ConnectionCoefficients Direction A`. They are not spacetime directions.
Each coefficient retains two independent operator-valued scalar slots and two
independent three-component operator-valued vector slots. `FourPotential` is
only a legacy four-label specialization, not a dimension of state space.
The four Zorn fields are internal algebraic slots. The projective construction
and its state-variation directions are in
`docs/PROJECTIVE_ZORN_ATTENTION_RECONSTRUCTION.md`.
No equality of the diagonal slots, identification of the two vector slots,
single-colour restriction, electrostatic reduction, or Cartan restriction
is imposed.

## Existing source owners reused

- `Physics/NCG/NoncommutativeChiralZornAlgebra.lean`: ordered full Zorn product.
- `Canonical/ThreeColorOperatorCrossCommutator.lean`: ordered dot/cross,
  coefficient commutators, all four Zorn coordinate blocks.
- `Canonical/OperatorZornConnectionCurvatureBridge.lean`: constant-connection
  curvature in the self-cross terms and the metric-plus-curvature square.
- `Canonical/OperatorZornRepresentationCurvatureBridge.lean`: coefficient
  transport through ring homomorphisms, without changing the Zorn product.

Related source boundaries are in `Algebra/AkivisIdentity.lean`,
`Canonical/NCZornAkivisIdentity.lean`, `Canonical/CanonicalZornBianchiDefect.lean`,
and `Canonical/NCZornAlternativityAudit.lean`. The new right-nested Akivis
identity is specialized directly to the actual NC coordinate carrier; it
requires no new nonassociative-ring instance or alternativity hypothesis.

## Noncommuting coefficient differential calculus

For an operator p in A, define delta_p coefficientwise by [p, -]. Its
additivity and product rule for the actual Zorn product are proved from
coefficient multiplication. In particular,

    [delta_p, delta_q] X = delta_[p,q] X.

No hypothesis declares the background operators P_mu to commute.
They may be differential operators in a suitable operator algebra, but
this algebraic construction does not by itself construct an unbounded
operator domain or a manifold derivative realization.

Write X star Y for the native Zorn product and

    as(X,Y,Z) = (X star Y) star Z - X star (Y star Z).

The direction-polymorphic algebraic calculus is

    nabla_mu X = delta_Pmu X + Phi_mu star X,
    F_mu,nu = delta_Pmu Phi_nu - delta_Pnu Phi_mu
               + Phi_mu star Phi_nu - Phi_nu star Phi_mu.

Its full curvature action is

    [nabla_mu,nabla_nu] X
      = delta_[Pmu,Pnu] X + F_mu,nu star X
        - as(Phi_mu,Phi_nu,X) + as(Phi_nu,Phi_mu,X).

All four terms are retained. The formula does not assert that curvature
is left multiplication by F alone. The proof performs ring normalization
only after reducing to individual expressions in the coefficient algebra;
it never invokes associativity of the Zorn carrier.

Legacy names E_i = F_0,i+1 and B = (F_23,F_31,F_12) select pairs of four
labels only. They carry no temporal, spatial or physical electromagnetic
interpretation. The general curvature and Bianchi theorems have no fixed
index cardinality. The full Zorn-valued expressions are unchanged.

## Bianchi / Akivis source

With nabla^ad_mu X = delta_Pmu X + [Phi_mu,X]_star, the cyclic Bianchi
expression is proved equal to

    delta_[Pmu,Pnu] Phi_rho
      + delta_[Pnu,Prho] Phi_mu
      + delta_[Prho,Pmu] Phi_nu
      - Alt(as)(Phi_mu,Phi_nu,Phi_rho).

Here Alt(as) is the full signed six-term alternation. No Jacobi identity
is imposed on the Zorn commutator. No reduction to six times one
associator is made for general noncommuting coefficients.

## Gauge covariance and the frame term

A coefficient ring homomorphism is applied to all eight entries and
preserves the full Zorn product, associator, derivative, field strength,
curvature action and Bianchi expression.

For a unit g of A, coefficient conjugation gives a bijective gauge map
G_g on the same Zorn carrier. The connection pair transforms as

    P_mu' = g P_mu g^-1,
    Phi_mu' = G_g(Phi_mu),
    X' = G_g(X).

The inhomogeneous connection-generator term is proved explicitly:

    g P_mu g^-1 = P_mu - [P_mu,g] g^-1.

This term is not dropped. If g is realized as multiplication by a varying
frame and P_mu as a derivative operator, [P_mu,g] supplies the derivative
of that frame; that realization needs its own domain/product-rule theorem.
The implemented transformation changes the pair (P,Phi). It must not be
misreported as a universal fixed-background formula for Phi alone.

G_g preserves associators and satisfies the corresponding curvature and
Bianchi covariance identities. It is a coefficient-unit gauge family,
not a proof that all automorphisms of the native split-octonion carrier
are coefficient-inner. General moving Zorn-frame/derivation connections
remain a distinct construction; neither their terms nor their existence
are silently inferred from this family.

## Verification

The two new modules contain 29 theorem statements with complete proof
scripts. Native Lean compilation was attempted through the supplied
check script but could not run because Lake is unavailable in the
authoring container. No successful elaboration or transitive axiom
verification is claimed. The PR remains draft.

The independent regression uses exact free, noncommuting coefficient
words with rational coefficients, and mutual inverse letters g/G.
The Zorn product itself is never reassociated. Sixteen identities, comprising
116 coordinate checks, passed. This is not a Lean certificate.

The source archive includes the reproducible check and JSON report:

    python3 tools/quality/check_operator_zorn_gauge_algebra.py

On an idle complete repository checkout with the pinned dependencies:

    bash scripts/quality/check_operator_zorn_gauge.sh

The latter performs a narrow build and a fresh transitive-axiom readout
for all 29 theorem names. No dependency update or cache cleaning occurs.
