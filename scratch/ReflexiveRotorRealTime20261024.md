# Reflexive rotor real-time candidate

Source: `ReflexiveRotorRealTime20261024.lean`, frozen source-only candidate.
Grounding contract: `ReflexiveRotorRealTimeContract20261024.md`.
Pending native dependency: `InfoGeometry.Canonical.ReflexiveRotorMotion`;
algebraic v4 is separately frozen and awaiting QA/promotion. Do not compile this
consumer before that dependency is promoted and the shared QA lane is assigned.

## Exact native constructions

Only new function: realRotor d B t = existing rotor (Real.cos t) (Real.sin t) d B.
The conjugated path is the EXISTING ModularFlowGeneratorDerivative.conjugationPath
with U=realRotor d B and V(t)=realRotor d B (-t). No duplicate conjugation function,
carrier, pair structure, unitary assertion, or bundled analytic law is introduced.

Ambient assumptions: NormedRing A, NormedAlgebra ℝ A. No CompleteSpace A.
Coefficient differentiation and continuity require no pair assumptions.
Generator/commutator identifications use only d²=B²=0, dBd=d, BdB=B.

## Actual proof chain

hasDerivAt_realRotor_coefficients differentiates the finite sine/cosine expression
with Real.hasDerivAt_cos/sin, HasDerivAt.smul_const/add, and the constant rule.
continuous_realRotor and continuous_rotorOrbit prove actual continuity.

realRotor_generator_left/right reuse native support_mul_skew, skew_mul_support,
and skew_square from UnipotentReflexivePairFactorization, together with the
native complement formula. This gives U'=J*U=U*J, J=d-B.
hasDerivAt_reverseRotor uses the real negation chain rule to prove V'=-V*J.

hasDerivAt_rotorOrbit REUSES native hasDerivAt_conjugationPath with these proved
derivatives, yielding P'=[J,P] for every ambient starting X. No derivative or
flow property is assumed. hasDerivAt_plus_zero specializes X=dB and the native
skew_commutator_plus to prove the initial velocity -(d+B).

lieBracket_rotorOrbit transports brackets because the actual U,V commute with J.
hasDerivAt_deriv_rotorOrbit first identifies the function deriv(path) using the
proved first derivative at every time, then differentiates the commutator with
constant multiplication/subtraction. Thus it proves an actual second derivative,
not just a ring identity relabeled as a differential equation.

rotorOrbit_parity uses the normalized native moving-projector sum and
Real.cos_sq_add_sin_sq to obtain G(t)=2*P(t)-Delta.
double_commutator_parityOrbit and double_commutator_plusOrbit transport the
algebraic brackets and obtain -4G and 2Delta-4P respectively.
hasDerivAt_deriv_parityOrbit and hasDerivAt_deriv_plusOrbit substitute those
values into the actual second derivative. Here Delta=existing support d B.
The proof never incorrectly equates the projector second derivative to -4P.

## Audit boundaries

No exponential identification, ODE uniqueness, Stone theorem, positivity,
self-adjointness, or de Bruijn claim. Unless additional star hypotheses are
proved, the normalized moving objects are idempotents, not star projections.
All results concern the actual native sine/cosine rotor; no supplied analytic
premises or fixed scalar parameters reused across distinct times.

No builds/tests/live edits/budget changes. Algebraic v4 and FreshTail are untouched.
Independent AA and serialized kernel QA remain required; this file has not been
compiled. Suggested audit heads: hasDerivAt_realRotor_coefficients,
continuous_rotorOrbit, hasDerivAt_reverseRotor, hasDerivAt_rotorOrbit,
hasDerivAt_plus_zero, hasDerivAt_deriv_rotorOrbit,
hasDerivAt_deriv_parityOrbit, hasDerivAt_deriv_plusOrbit.
