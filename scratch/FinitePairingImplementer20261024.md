# Finite circular pairing implementer: G-A sandbox contract

Status: UNCOMPILED candidate, 2026-10-24. No tests, Lean commands, or builds
were run. No acceptance or axiom report is claimed. Parent promotion and
independent A-A/QA remain required.

## Source grounding and bounded gap

Inspected native owners include Algebra/ChiralCARTransport (pairing-current
commutators and explicit star-duality), OperatorAlgebra/QuadraticRotorUnit
(generic scalar-square rotor unit/sandwich), Algebra/ChiralRealHyperbolicRotor
(real boost and fixed-star defect), OperatorAlgebra/ChiralRealBivectorRotor
(conjugation covariance), Physics/NambuSpinorGrassmannian (primitive two-mode
CAR, support products, Cooper-pair nilpotence), and the signed/thermal CAR
owners. Broader searches included Physics/HyperbolicBogoliubovRotation
(categorical doublet involutions), Canonical/BogoliubovClosedForms (normed
operator scalar-square exponentials), BogoliubovBasisConjugation (transport of
a supplied basis), and BogoliubovFockSuper (doubled projector-super and CAR
interfaces). These cover related constructions but the inspected statements
do not give this primitive two-mode finite pairing polynomial action. This is
not a repository-wide uniqueness/absence certificate.

Existing SignedBogoliubovCAR and ChiralCARTransport already cover all output
CAR brackets and squares. No new preservation packet is proposed.

## Primitive contract

The ambient carrier is arbitrary `[Ring A]`. The scalar part uses
`[CommRing R] [Algebra R A]`, so scalars commute with all ambient operators.
Inputs are four operators p,P,q,Q, with these ten separate hypotheses:

```
p*p=0, P*P=0, q*q=0, Q*Q=0
p*P+P*p=1, q*Q+Q*q=1
p*q+q*p=0, P*Q+Q*P=0, p*Q+Q*p=0, q*P+P*q=0
```

No output action, support property, inverse law, or nontriviality is assumed.
There is no characteristic restriction, division by two, analytic exponential,
new carrier, or CAR witness structure.

Definitions in the candidate:

```
T = q*p - P*Q
Pi = (q*p)*(P*Q) + (P*Q)*(q*p)
R(c,s) = 1 + (c-1) • Pi + s • T
```

Separate target declarations derive from the primitive relations:

- `pairSupport_eq_occupancy`: Pi = (p*P)*(q*Q) + (P*p)*(Q*q).
- `current_sq`: T*T = -Pi.
- `pairSupport_sq`: Pi*Pi = Pi.
- `pairSupport_mul_current` and `current_mul_pairSupport`: Pi*T=T and T*Pi=T.
- `rotor_mul_reverse`: R(c,s)*R(c,-s) = 1+(c*c+s*s-1) • Pi.
- `rotorUnit`: a native A unit under c*c+s*s=1, with both inverse orders.
- Four separate sandwich actions:
  p -> c • p+s • Q; Q -> c • Q-s • p;
  q -> c • q-s • P; P -> c • P+s • q.

The sandwich polynomial identities themselves do not need normalization:
normalization is needed to call the reverse factor an inverse. The complement
of Pi retains its identity action. T is not assumed to square to minus the
ambient identity; therefore blindly instantiating QuadraticRotorUnit with T
would not establish this result.

## Proof and reuse boundary

Five private elementary word-reduction helpers derive directly from square-zero,
normalization, and anticommutation. Conditional simplification uses only the
primitive hypotheses, normal-ordering words as Q,P,q,p. Ring/module normalization
then handles sums and central coefficients. This is a proposed Lean proof
strategy, not tested elaboration. In particular conditional simp matching,
scalar normalization, automatically included section parameters, and unused
hypothesis warnings need checking before any promotion. No proof holes or
axioms were inserted to conceal these obligations.

The existing ChiralCARTransport current commutators fix the sign convention;
the finite polynomial action is additional to those infinitesimal identities.
This draft imports that owner and does not duplicate its commutator theorems.
It does not add a redundant AlgEquiv wrapper: parent can reuse the native
inner-conjugation API with rotorUnit if a consumer needs an equivalence.

Star is outside the candidate. Existing pairing_current_star gives star T=-T
under P=star p and Q=star q. To identify reverse rotor with star rotor also
requires a compatible scalar star and self-adjoint c,s; CAR alone supplies none
of those hypotheses. No positive-Hilbert unitarity, Spin/Pin classification,
analytic implementability, or hyperbolic implementation is claimed.

The local section retains all ten primitive hypotheses on the CAR-derived
lemmas for reviewability. Any warning cleanup/minimization must preserve the
same full two-mode consumer contract; it must not replace missing derivations
by assuming Pi identities or output actions.
