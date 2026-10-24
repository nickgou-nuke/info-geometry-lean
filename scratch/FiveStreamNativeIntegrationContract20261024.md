# Five-stream native integration: bounded source contract

Source-only navigation and proposed small consumer delta; no builds or kernel
receipt. No Lean implementation in this task. Colimit implementation belongs
to the parent and is explicitly outside this proposed draft.

## Current source and concurrent work

At inspection, DeBruijnRotorAlternationCycle.lean was staged as added and
FiveStreamMasterIntertwiner.lean was untracked. The latter ALREADY contains
many proposed cross-stream statements. This is source coverage, not evidence
of its successful compilation. Preserve the foreign file; do not duplicate its
omnibus theorem, carriers/coherence conjunction, archetypes, or compiler packet.

The five owners, all in Canonical:
1. GrassmannianBundleCyclotomicOrientability: lieBracket X Y=XY-YX (47),
   homogeneousProj g ginv P=g*P*ginv (50),
   isIdempotentElem_homogeneousProj (56) assumes P²=P and ginv*g=1.
   unitOrbitMap P (g:Aˣ)=homogeneousProj g (g⁻¹) P (579);
   unitOrbitSetoid/QuotientEquiv (583/586) are the existing orbit quotient.
   unitOrbitMap_eq_self_iff (595) characterizes the stabilizer as gP=Pg;
   unitOrbitMap_fiber_iff (606) compares orbit fibers via h⁻¹*g.
2. RootsOfZeroUnityMoebiusModularG22: polePlus=dB, poleMinus=Bd,
   activeSimplex=dB+Bd, harmonicZeroPole=1-activeSimplex,
   chiralParityRoot=dB-Bd, diracRootPlus=d+B, hodgeStarRootMinus=d-B;
   moebiusWeylInversion=P0+(d-B), inverse=P0-(d-B).
3. UnifiedGeometryOperatorSignificance: projPlus/projMinus=dB/Bd (93/96),
   hodgeLaplacian and projHarmonic (99/102), ehresmannCurvature=dB-Bd (105),
   kahlerStructure=d-B (108), bruhatWeylReflection=P0+J (117),
   kmsModularWeight u v=(u*u) • Bd+(v*v) • dB (123).
   It already imports ReflexiveNilpotentFlows and PeirceWeightedTrace.
4. ModularParabolicCyclotomicSynthesis: IsDualRootOfZeroPair (77) has exactly
   d_sq, B_sq, dBd, BdB. bruhatQuarticOp=(1+d)(1-B)(1+d) (102).
   bruhatQuarticOp_eq_zeroMode_add_sub (223) proves P0+J from the pair;
   its inverse and pole-conjugation laws are already proved in source.
5. DeBruijnRotorAlternationCycle: IsDualSeedPair (72) has exactly the same
   four primitive fields, no desired motion conclusions. polePlus/Minus (79/82),
   carrierSupport (85), zeroModeSupport (88), phasePolarization (91),
   transitionVelocity (94), wheelGenerator (97), phaseRotor (100),
   movingPolePlus/Minus (104 onward) are the same raw expressions.
   Existing source covers explicit moving formulas, idempotence, sum,
   bracket oscillator, and no-turn. Do not prove these primitives again.

ReflexiveNilpotentFlows owns the raw-four-hypothesis support/complement/rotor,
rotor_mul and rotor_inverse. Native ReflexiveRotorMotion owns generalized
conjugation, idempotence/orthogonality/sum, quarter-turn and no-turn. Native
ReflexiveRotorRealTime now differentiates the actual sin/cos curve using the
existing ModularFlowGeneratorDerivative.conjugationPath; its scope is normed
real algebras, not arbitrary rings or a supplied exponential.

PeirceWeightedTrace.supportWeight a b d B = a • Bd+b • dB (arbitrary central
weights). weight_eigenproducts, weight_intertwining, weighted_trace_boundary
already provide the division-free boundary. TracialCARDensity.weighted takes
native NCG.TracialFunctional R A and is tau.toLinearMap.comp(mulLeft R rho).
Its inverse_pullback and joint_covariance already transport weighted readouts
by an actual unit. No new trace structure is needed.

## Existing concurrent cross-owner coverage: do not reauthor

FiveStreamMasterIntertwiner currently declares:
- isDualRootOfZeroPair_iff_isDualSeedPair (69), direct four-field equivalence;
- movingPolePlus_is_grassmannian_homogeneousProj (97), definition + idempotence;
- grassmannian_peirce_extracts_seeds_and_horizontal_velocity (108);
- phaseRotor_quarter_turn_eq_bruhatQuarticOp (146), also Stream2/3 Weyl equality;
- tracial_vanishes_on_dual_seeds (231), derived by cyclicity and square zero;
- kmsModularWeight_mul_movingPolePlus (244), full weighted product;
- tracial_kms_movingPolePlus_interpolation (277), squared-weight scalar formula;
- jordanLeft_commutator_intertwines_velocity_and_wheel (291).

The predicate implication and quarter-turn equality are already explicit there.
Their mathematical status must be checked independently, not inferred from file
prose saying certified. Reuse accepted versions or extract small owner-aligned
pieces in coordination; no second implementation is warranted just from names.

## Smallest useful proposed integration surface

Use abbreviations S1...S5 ONLY in this report for the five namespaces, not Lean
carrier/definition aliases. Common scope [CommRing R] [Ring A] [Algebra R A].

A. Definition equalities with actual consumers (no standalone certificate):
  S5.phaseRotor c s d B = ReflexiveNilpotentFlows.rotor c s d B
  S5.movingPolePlus c s d B = S1.homogeneousProj
    (ReflexiveNilpotentFlows.rotor c s d B)
    (ReflexiveNilpotentFlows.rotor c (-s) d B) (d*B)
  S3.kmsModularWeight u v d B = PeirceWeightedTrace.supportWeight (u*u) (v*v) d B.
All are definitional readbacks. Add only those consumed by substantive statements
below, not a new list of synonyms. Map h:S5.IsDualSeedPair to the S4 predicate
using the existing field equivalence; raw native APIs use h.d_sq/h.B_sq/h.dBd/h.BdB.

B. Stream1 unit orbit, stronger than existing homogeneousProj readback:
  h:S5.IsDualSeedPair d B, hc:c*c+s*s=1 imply
  S5.movingPolePlus c s d B ∈ Set.range (S1.unitOrbitMap (d*B)).
Construct a LOCAL term u:Aˣ with val=canonical rotor c s and inv=rotor c (-s),
using native rotor_inverse and rotor_reverse_inverse. Then the actual orbit
image is definitionally the moving projector. This uses the existing unit orbit
and quotient machinery; no new rotor-unit structure or orbit carrier is needed.
A useful additional consumer is its stabilizer equivalence for the moving
projector via unitOrbitMap_eq_self_iff, if required; do not repeat idempotence.

C. Actual rotation of the Stream3 density, not just its product with a projector:
For arbitrary a,b,c,s:R and the primitive pair, let U=canonical rotor c s,
V=canonical rotor c (-s). Prove the new operator equality
  U * PeirceWeightedTrace.supportWeight a b d B * V
   = (a*(s*s)+b*(c*c)) • (d*B)
     + (a*(c*c)+b*(s*s)) • (B*d)
     + ((a-b)*(c*s)) • (d+B).
No circle normalization needed for this polynomial formula. Proof: linearity
of multiplication/scalars and native rotor_conjugate_plus/minus. This identifies
how the existing static density acquires an off-diagonal part under actual
motion; specialize a=u*u,b=v*v for Stream3, without a duplicate definition.
This operator conjugation formula was not found in the inspected master/weight
owners; their existing product/interpolation theorem is a different statement.

D. Trace consumer, preferably coupled to C rather than duplicate interpolation:
Under hc and native tau:NCG.TracialFunctional R A, use the local actual unit and
TracialCARDensity.joint_covariance to prove invariance of the weighted readout
when BOTH the Stream3 density and Stream5 moving observable are transported.
For example rotated density paired with movingPolePlus equals tau(W*dB),
then weight_eigenproducts/support_table give the explicit b*tau(dB).
Fixed-density readout of a moving projector is generally NOT invariant:
its interpolation is already in the concurrent master file. Do not confuse
that law with simultaneous conjugation covariance. No positivity, normalized
state, faithful density, or analytic KMS hypothesis is supplied or concluded.

E. Optional meaningful Stream5 analytic consumer, if requested beyond this draft:
Read movingPolePlus(cos t,sin t) as the actual native conjugationPath and use
ReflexiveRotorRealTime.hasDerivAt_rotorOrbit/hasDerivAt_plus_zero, not a new
continuity axiom. This requires NormedRing/NormedAlgebra real scope; it is not
implied by the Stream5 docstring calling the polynomial rotor continuous.

## Other native consumers and parent-owned colimit handoff

PeirceWeightedTrace is consumed by KitaevNativeCARDensity and
KitaevBoundaryWeights as well as Stream3 and its audit. Its general unsquared
weight API is the appropriate shared owner for C/D, avoiding an isolated
five-stream master module. Native motion/real-time owners are narrow and do not
import the foreign master. The inspected Stream5 dependents are its Audit and
the concurrent master; that is bounded import evidence only.

Categorical map read. Parent-owned extension can use an actual AlgHom to preserve
raw pair laws, rotor polynomial and supportWeight (RingHom suffices only without
external scalar coefficients). Existing CuntzMatrixAlgebraicStarColimit has
rawMap : MatrixStage i →⋆ₐ[ℂ] MatrixStage j and
stageInjection i : MatrixStage i →⋆ₐ[ℂ] Carrier (99).
FilteredStarAlgebraDirectLimit owns AlgebraicStarDirectLimit,
algebraicStarDirectLimitOf Stage sys i : Stage i →⋆ₐ[ℂ] AlgebraicStarDirectLimit,
algebraicStarDirectLimitOf_transition and liftStarAlgHom for compatible maps.
Do not construct another colimit or assume arbitrary ring A has an injection
into this particular matrix tower. Real-time derivative transport needs a
continuous linear/algebra map and an appropriate normed target; algebraic
colimit transport alone supplies no topology. All colimit implementation is
excluded from this author assignment per parent coordination.

Recommended minimal implementation: one narrow weight-motion consumer with
local native unit/orbit use, plus only the definition readbacks it consumes.
Coordinate the already-written predicate/quarter-turn pieces with the concurrent
author. No omnibus result, certificate, duplicate primitive, or grand wrapper.
