# Complex-time conjugation: generic analytic substrate

Author Popper; source-only uncompiled candidate requiring separate AA and QA.
New source ComplexTimeConjugation20261024.lean. No live edits or builds.
This implements the generic portion of steps 2/3 in
FiniteSeedAnalyticKMSContract20261024.md; not its concrete state boundary.

## Exact construction and scope

For an existing arbitrary CStarAlgebra A, G,x:A, z:Complex, define only
alpha G z x = exp((z*I) • G) * x * exp(-((z*I) • G)).
No new carrier, state, norm, compatible-family package or analytic premise.
Seven named lemmas plus this one definition:

- alpha_analyticAt: the actual orbit is complex analytic at EVERY complex z.
  Scalar multiplication and multiplication preserve analyticity, and the native
  Banach-algebra exponential is entire. No hypothesis assumes the conclusion.
- alpha_ofReal: exact equality to the existing REAL-domain
  ModularFlowExponentialGenerator.complexExponentialConjugationPath.
- alpha_ofReal_eq_unitary: for G:selfAdjoint A reuse the accepted
  FiniteExponentialMotion owner theorem expUnitary_conjugation_eq_complexPath.
  Positive-time exp(i*t*G) is preserved; no duplicate normalization proof.
- exp_time_add: commuting scalar multiples of G give the exponential product.
- alpha_add: alpha(z+w,x)=alpha(z,alpha(w,x)); the inverse exponential factors
  are reversed. No commutation with x is assumed.
- alpha_imaginary: at +i*beta the first exponential is exp(-beta • G), and the
  second is exp(+beta • G), for every real beta.
- alpha_add_imaginary: derive the shifted-orbit conjugation identity for every
  complex z by time addition, preserving the same sign convention.

G need not be self-adjoint for entire analyticity, composition or imaginary
evaluation. Self-adjointness is needed only for the real-axis unitary readback.
No star-automorphism claim is made for complex time. Completeness is inherited
from CStarAlgebra A. Rational normed scalar restriction is the native
NormedAlgebra.restrictScalars ℚ ℂ A, locally used for exp_add_of_commute only.
No budgets, transparency settings, extra instances on raw matrices or unsafe APIs.

## Grounded APIs

- Native Canonical/FiniteExponentialMotion.lean:
  InfoGeometry.OperatorAlgebra.expUnitary_conjugation_eq_complexPath.
  Read SHA 93f2c6b5af7f729693d1aac9eb574d4109c270042993167906525982426a4541.
- Native Canonical/ModularFlowExponentialGenerator.lean: actual real-domain
  complexExponentialConjugationPath, positive sign definition at line48.
- Pinned Mathlib Analysis/Normed/Algebra/Exponential.lean:
  NormedSpace.exp_analytic (498), exp_add_of_commute (520).
- Analysis/Analytic/Constructions.lean: AnalyticAt.smul (623), mul (650), neg;
  Analysis/Analytic/Composition.lean: AnalyticAt.comp (859).
- RCLike.real_smul_eq_coe_smul identifies real and embedded-complex actions.

## Deferred concrete obligations

Specialize to the ACTUAL representedCStarClosure, native seedGenerator and
seedStageHom, with explicit native instance alignment if needed. Consume the
separate density-exponential bridge only after its QA acceptance; it is not
an assumed premise or an import here. Then derive the scalar state boundary
from finiteSeed_representedVacuumTwistedCyclic and actual state readback.
Uniform boundedness on an upper strip still needs beta>0 and its own proof.
Entire analyticity alone is not strip boundedness. No analytic KMS acceptance,
state faithfulness, growing Hamiltonian, or represented motion acceptance here.
