# Real-time native reflexive rotor: bounded analytic contract

Contract only; no new Lean proof, build, or kernel receipt. RotorMotion v2 stays
frozen. This is a proposed analytic consumer of its algebraic identities.

## Carrier, hypotheses, and exact functions

Use {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]. No CompleteSpace A.
For derivative identifications assume only the same four primitive laws:
d*d=0, B*B=0, d*B*d=d, B*d*B=B.
Use existing ReflexiveNilpotentFlows.rotor/support/complement and
GrassmannianBundleCyclotomicOrientability.lieBracket. No replacement carrier.
For contract notation only:
  J=d-B; Q=d+B; Delta=support d B; Gamma=d*B-B*d;
  U(t)=rotor (Real.cos t) (Real.sin t) d B;
  V(t)=rotor (Real.cos t) (-Real.sin t) d B;
  P(t)=U(t)*(d*B)*V(t);
  G(t)=U(t)*Gamma*V(t).
These functions are actual formulas, not supplied paths with derivative axioms.
U uses t, not the half-angle convention of ChiralRealBivectorRotor.

## Existing source and reuse boundaries

Canonical/ReflexiveNilpotentFlows.lean: rotor (133), rotor_mul (226),
rotor_inverse (248), support_table, complement_annihilates. The polynomial
formula is universally quantified in its coefficients before specialization.
Pending scratch ReflexiveRotorMotion20261024v2.lean supplies explicit projector
conjugation, inverse order, idempotence/orthogonality/sum, and algebraic brackets.
Its QA is separate; this contract does not call it already kernel-accepted.

OperatorAlgebra/ChiralRealBivectorRotor.lean defines the full-support half-angle
rotor cos(theta/2)*1+sin(theta/2)*B. It does not replace the native proper-support
rotor P0+cos(t)*Delta+sin(t)*J, and its inspected source supplies no HasDerivAt
proof for the present path.
Canonical/ModularFlowExponentialGenerator.lean:17-37 already proves
hasDerivAt_exponentialConjugationPath_zero under CompleteSpace A, for actual
NormedSpace.exp. Its carrier/path and completeness requirements differ; do not
import that hypothesis merely to differentiate our finite sin/cos formula.
Canonical/FilteredGNSBoundedGeneratorUnitaryFlow is a CStar/unitary flow owner,
not an identification of an arbitrary reflexive pair with an adjoint pair.
Bounded searches of reflexive owners and rotor/derivative consumers found no
exact present analytic bridge; this is not a repo-wide absence assertion.

## Source-verified mathlib APIs

Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean:
Real.hasDerivAt_sin (322): HasDerivAt sin (cos t) t;
Real.hasDerivAt_cos (363): HasDerivAt cos (-sin t) t.
Trigonometric/Basic.lean: Real.continuous_sin, Real.continuous_cos.
Real.sin_sq_add_cos_sq gives normalization (reorder and rewrite sq as mul).
Mathlib/Analysis/Calculus/Deriv/Mul.lean:
HasDerivAt.smul_const (149): hc -> derivative c' • a of t -> c(t) • a;
HasDerivAt.mul (256): derivative f'(t)*g(t)+f(t)*g'(t), in that order;
HasDerivAt.mul_const (293), HasDerivAt.const_mul (345).
Its multiplication section requires NormedRing/NormedAlgebra, not completeness.
Deriv/Add.lean: HasDerivAt.add (59), .neg (264), .sub (356).
Deriv/Basic.lean: hasDerivAt_const (803).
Use Continuous.add/smul/mul or pointwise HasDerivAt.continuousAt to establish
actual continuity. No continuity premise is added to the proposed theorem.
Suggested imports: native algebraic motion owner once promoted,
Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv and
Mathlib.Analysis.Calculus.Deriv.Mul (plus Deriv.Add if not transitively exposed).

## Small proposed theorem sequence

1. Continuous U and Continuous P. These polynomial/trigonometric continuity
   results do not need the four pair relations.
2. For every t, derive HasDerivAt U
     ((-Real.sin t) • Delta + Real.cos t • J) t
   using the scalar and addition rules. Similarly derive V's derivative
     (-Real.sin t) • Delta - Real.cos t • J.
3. Use native support absorption, J²=-Delta, and complement annihilation
   to identify U'=J*U=U*J and V'=-V*J. These are actual derived identities.
4. Apply the noncommutative product rule twice to P. Associativity gives
     HasDerivAt P (lieBracket J (P t)) t.
   Initial value P(0)=d*B follows from native rotor at (1,0).
   Specialize the derivative at zero and reuse skew_commutator_plus to obtain
     HasDerivAt P (-(d+B)) 0.
   The initial derivative is -Q, not +Q and not a constant velocity at all t.
5. Differentiate t -> lieBracket J (P t) with const_mul, mul_const, sub:
     HasDerivAt (fun t => lieBracket J (P t))
       (lieBracket J (lieBracket J (P t))) t.
   A deriv(deriv P) formulation may then use .deriv; prefer the explicit
   HasDerivAt statement first so differentiation is proved, not inferred.
6. For G, prove HasDerivAt G [J,G(t)] and
     [J,[J,G(t)]]=-(4:A)*G(t).
   Transport the algebraic Gamma identity through U,V, which commute with J,
   or specialize the explicit formulas. Thus G''=-4G as an actual derivative
   consequence. G(0)=Gamma and G'(0)=-2Q.
7. For P the correct second derivative is 2*Delta-4*P(t), not -4*P(t).
   Derive G(t)=2*P(t)-Delta using the normalized moving projector sum;
   alternatively directly conjugate [J,[J,dB]]=-2*Gamma. No scalar division
   is required for the algebraic version.

Normalized idempotence, mutual zero products, and fixed sum follow from the
already specified algebraic motion lemmas plus the real circle identity.
Do not assume those outputs. Without B=star d and an appropriate star algebra,
these are idempotents rather than orthogonal/self-adjoint projections.

## Explicit limits of this contract

No completeness is needed for these finite combinations or derivative rules.
Identifying U(t) with NormedSpace.exp(t • J) is a separate theorem requiring
the appropriate convergence/completeness APIs; it is not assumed or asserted.
No abstract ODE uniqueness, Stone theorem, de Bruijn syntax claim, or physical
classification follows merely from the ring oscillator identity. The requested
analytic bridge must prove HasDerivAt on the actual native formulas above.
