# Hestenes–Krein Weyl generator contract

## Requested scope

Continue in the native real geometric/Krein language, not logarithmic functional
calculus or complex continuation. Establish the algebraic infinitesimal action
and inversion covariance on actual doubled-space endomorphisms.

## Carriers and conventions

- `DoubledSpace E = WithLp 2 (E × E)` for a complete real inner-product space E.
- Existing `modular_j (x,y)=(y,x)` is the split generator G, G²=1.
- Existing `spectral_epsilon (x,y)=(x,-y)` determines the installed Krein metric.
- Existing `complex_i (x,y)=(-y,x)` is W, W²=-1, W⁻¹=-W.
- G is Krein-skew (`DoubledAdjoint.modular_j_kreinSkewAdjoint`). Do not mistake
  spectral_epsilon for a skew generator of its own fixed metric.
- `Krein.Representation.cl11Rep` sends the positive/negative Clifford vectors
  to G/W and their ordered product to spectral_epsilon. No new carrier.
- Existing `OperatorAlgebra.hyperbolicRotor G c s = c • 1 + s • G`,
  reverse `c • 1 - s • G`; normalization `c*c-s*s=1`.
- Existing `OperatorAlgebra.kreinCommutator G X = G*X-X*G` already has
  Leibniz and Krein-adjoint compatibility proofs.

## Small source-confirmed target

1. Over any ring A, the unit `1 + ε G` in Mathlib `DualNumber A` has inverse
   `1 - ε G`; conjugating `X + ε Y` gives `X + ε (Y + G*X-X*G)`.
   This is a first-order algebraic identity, not a convergence statement.
2. On the native doubled carrier, the already-defined hyperbolic rotor has
   Krein adjoint equal to its reverse; normalized coefficients give an actual
   unit and a Krein isometry, derived rather than hypothesized.
3. Native W conjugates G to -G, reverses the rotor, and reverses the commutator
   action by intertwining. The Clifford representation transports the
   commutator and rotor formulas into this same operator algebra.
4. Connect the generic dual-number result directly to native kreinCommutator.

## Search and reuse

Read owners: `Krein/DoubledSpace`, `DoubledAdjoint`, `Representation`,
`OperatorAlgebra/KreinInnerDerivation`, `Algebra/ChiralRealHyperbolicRotor`,
`Clifford/Hestenes`, and the Hestenes modular/rotor-boundary owners.
Repository-wide text search covered first-jet/dual-number conjugation,
hyperbolic rotors, modular generators, adjoint and Weyl laws. Existing
`ReflexiveFlowUnits` already owns diagonal-unit inversion; do not reimplement it.
The general rotor multiplication and reverse laws already exist and are reused.
The specific operator/first-jet coupling above is the bounded task, not a claim
of repository-wide novelty. CAS checks use the native coordinate order (x,y),
column-vector left action and ordinary left-to-right operator multiplication.

## Nonclaims

No full Tomita reconstruction, state classification, universal modular-flow
classification, global projective quotient, or new continuum construction.
W preserves the null locus but reverses the sign of this fixed Krein form;
do not declare it a Krein isometry. Its projective coordinate readout is
z -> -1/z; W itself has square -1, not 1. A normalized polynomial rotor is not
by itself a selected additive-time parametrization. No dependency pins change.
