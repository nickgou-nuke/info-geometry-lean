# Finite Fock realization: narrow implementation contract

Source research only; no compilation, tests, live edits, or new mathematical certificate.
Proposed native owner: `InfoGeometry.Clifford.FiniteFockReflexiveRotor`.
This is a substantive connection to the existing Fock implementation in this repository;
no external repository identity or transport map has been specified or verified.

## Actual carrier and imports

Use `InfoGeometry.Clifford.SpinorSpace (Vector n)` with the existing local
`fockNormedAddCommGroup` and `fockInnerProductSpace` instances, and its actual
real continuous endomorphism algebra `H →L[ℝ] H`. Do not assign a normed-ring
structure to exterior multiplication itself. No replacement Hilbert carrier.

Imports:
- `InfoGeometry.Clifford.FiniteRealFockNormBounds`
- `InfoGeometry.Canonical.DeBruijnRotorAlternationCycle`
- `InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis`
- `InfoGeometry.Canonical.ReflexiveRotorRealTime`

For `i : Fin n`, set notation D = `fockIntActionCLM n i` and C =
`fockExtActionCLM n i`, in namespace
`InfoGeometry.Clifford.ClNNNeutralChevalleyBridge`. Choose d=D, B=C throughout.
The i binder correctly excludes a coordinate at n=0, without a new n>0 hypothesis.
No new pair carrier or structure storing conclusions is needed.

## Source-grounded gap and elementary proof inputs

`Clifford/FiniteRealFockNormBounds.lean:71–102` defines both CLMs, their exact
application readbacks and norm bounds. A repo-wide exact-symbol search found
these CLM names only in that owner, not an existing stream realization.
`Clifford/ChevalleySpinorBlueprint.lean` supplies `ext_sq_zero`, `int_sq_zero`,
and `ext_int_anticommutator` on the same SpinorSpace, plus its actual definitions
`extAction` (left Clifford multiplication) and `intAction` (contractLeft).
`FiniteRealFockAdjoint` supplies `fock_extAction_intAction_inner` for this metric.
This is a bounded search result, not a claim that abstract CAR realizations are absent.

Small separate lemmas to implement:
1. `fockIntActionCLM_sq_zero`, `fockExtActionCLM_sq_zero`: extensionality and
   the existing pointwise square-zero theorems.
2. `fock_coordinate_CAR`: D*C+C*D=1. Extensionality, native anticommutator,
   and `(LinearMap.proj i) ((Pi.basisFun ℝ (Fin n)) i)=1`.
3. `fock_coordinate_reflexive_int` and `fock_coordinate_reflexive_ext`:
   D*C*D=D and C*D*C=C. Multiply CAR by D/C and simplify square-zero;
   these are derived facts, not assumptions or added proof fields.
4. Construct the EXISTING `DeBruijnRotorAlternationCycle.IsDualSeedPair D C`
   and `ModularParabolicCyclotomicSynthesis.IsDualRootOfZeroPair D C` from 1–3.
   These interface adapters are secondary; the actual action and trajectory below
   are the new consumer, not a certificate packet.
5. Active support D*C+C*D=1; both stream complements are zero. Their plus
   projector D*C is coordinate-vacancy and minus C*D is coordinate-occupation.
   Coordinate-vacancy is not the full many-coordinate vacuum projector.

## Actual trajectory and direct application readback

Use the existing `ReflexiveRotorRealTime.realRotor D C t`, not a duplicate flow.
Prove the equality with Stream5 `phaseRotor (Real.cos t) (Real.sin t) D C`
by unfolding only the named support/rotor definitions. CAR gives the useful
operator equality R(t)=cos(t) • 1 + sin(t) • (D-C).

Required direct readback on every original spinor x:

    realRotor D C t x = cos(t) • x + sin(t) • (D x - C x).

For P(t)=Stream5.movingPolePlus (cos t) (sin t) D C, prove identity with
native `conjugationPath (realRotor D C) (fun t => realRotor D C (-t)) (D*C)`
and expose application:

    P(t) x = cos(t)^2 • D(C x) + sin(t)^2 • C(D x)
             - (cos(t)*sin(t)) • (D x + C x).

Reuse `ReflexiveRotorMotion.rotor_conjugate_plus` (namespace
`ReflexiveNilpotentFlows`) or Stream5 `movingPolePlus_eq`; do not re-expand CAR.
`rotor_plus_idempotent` and `rotor_projector_sum` give idempotency and
Pplus(t)+Pminus(t)=1 at these actual real parameters. These are algebraic
idempotents unless self-adjointness is separately derived from the native inner law.

Native real-time theorems already provide the stronger actual analytic content:
- `hasDerivAt_rotorOrbit`: P'(t)=[D-C,P(t)].
- `hasDerivAt_plus_zero`: P'(0)=-(D+C), with this exact sign.
- `hasDerivAt_deriv_plusOrbit`: P''(t)=2*1-4*P(t).
- `hasDerivAt_deriv_parityOrbit`: Gamma''(t)=-4*Gamma(t).
- `continuous_rotorOrbit`: operator-norm continuity.
These specialize by the four proved primitive relations; there is no assumed
trajectory field. `ReflexiveNilpotentFlows.rotor_mul` plus real trig addition
also yields R(t+u)=R(t)R(u), and its inverse theorem yields R(-t)=R(t) inverse.
The differential trajectory alone does not assert an already-packaged group action.

If nonconstant motion is included, derive it: the existing no-turning iff and
CAR force D+C nonzero on a nontrivial spinor space. Supply nontriviality from
the accepted exterior basis/real metric, rather than assuming the derivative
nonzero. Periodicity means this does not imply motion at every nonzero time.

## Stream4 shear bridge on precisely these same operators

Use `ModularParabolicCyclotomicSynthesis.parabolicHexalityOp` and
`bruhatQuarticOp`; the new proof-bearing content is their concrete action readback:

    parabolicHexalityOp D C x = x + D x - C x - D(C x),
    bruhatQuarticOp D C x = D x - C x.

The latter follows from `bruhatQuarticOp_eq_zeroMode_add_sub` and active-unit CAR.
Reuse its inverse, cube/sixth and square/fourth lemmas individually: double shear
has cube -1 and sixth 1; triple shear has square -1 and fourth 1. No exact-order
claim without a separate lower-order exclusion. The triple shear equals R(pi/2),
linking the discrete product and the actual continuous Fock rotor.
Shears need not preserve the inner product; do not call them unitary.
This is the minimal second consumer; a weighted trace is unnecessary for this batch.

## Five-stream and further-consumer boundary

Streams1/2 already use these same square-zero/reflexivity ring equations, so the
proved CLM equations supply genuine instances of their finite algebraic laws.
Stream1's quotient still targets its orbit, never all Grassmannians. Stream2's
Klein equation remains an operator sign relation, not a topological realization
or G2 automorphism. Stream3's star-support premises must be discharged from the
actual Fock inner-adjoint theorem before its star-dependent statements are applied;
plain CAR alone does not supply a StarRing/adjoint interface. A follow-up may prove
inner self-adjointness of D*C and C*D directly without introducing that interface.
The first batch must not claim all five semantic labels have been unified.
No Nambu fundamental identity, De Bruijn word cycle, analytic KMS state,
completed infinite Fock space, interacting tower, or other-repository map follows.

Keep proofs modular: a small CLM CAR/interface owner followed, if needed, by a
small rotor/shear consumer. No master conjunction. Parent AA and serial locked QA
remain required before any promotion or kernel acceptance claim.
