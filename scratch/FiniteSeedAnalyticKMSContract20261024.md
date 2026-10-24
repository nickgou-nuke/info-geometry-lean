# Actual finite-seed complex-time boundary: research contract

Source-grounded proposal, 2026-10-24. No implementation or compiler run; no
new theorem is certified here. This is the bounded next delta after the existing
represented algebraic twisted identity, not a claim that strip KMS is already proved.

## Exact carrier and data

Fix k : Nat, H : MatrixStage k, hH : H.IsHermitian, beta : Real, and vacuum
stage v : Nat. Set omega = finiteSeedCompatibleStageStates H hH beta and
C = representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem omega.
Use the existing complex C-star algebra C, not raw matrices with a fabricated
NormedRing instance and not a new Hilbert carrier.

J = FiniteSeedRepresentedRealTime.seedStageHom H hH beta;
G = (seedGenerator H hH beta : C) = J H;
delta = representedDensityUnit H hH beta : Cˣ;
phi = FilteredGNSVacuumReadback.representedVacuumFunctional ... omega v : C →L[ℂ] ℂ.
The actual representedVacuumState ... omega v has this same evaluation
functional, through representedVacuumPositiveFunctional. Work generically with
the continuous linear functional before specializing the dependent State type.

delta is the UNNORMALIZED mapped Gibbs density unit. The actual state is
normalized already; do not insert a second partition function into conjugation.
The raw seedDensityUnit mapped through algebraicColimitToRepresentedClosure
must be explicitly aligned with delta (Units.map composition), not replaced by
an unrelated unit.

## Minimal proof sequence

1. Prove the actual density/exponential bridge in C:
   (delta : C) = NormedSpace.exp ((-beta) • G), and its inverse equals
   NormedSpace.exp (beta • G). These are proof obligations, NOT assumptions
   in the final finite-seed theorem. Transport the finite Hermitian CFC along
   the native type-copy and represented star hom; use CFC composition/scaling
   and CFC.real_exp_eq_normedSpace_exp on the self-adjoint image. Establish
   continuity for each map used in map_cfc. CStarMatrix intermediates avoid
   requiring a nonexistent raw-matrix NormedRing instance. Alternatively derive
   continuity of the finite-dimensional raw-domain linear map explicitly.
   Inverse equality follows from the two exponential inverse laws and unit
   inverse uniqueness, not an independent inverse-density assumption.

2. Define only the complex-time function on this same C:
   alpha(z,X) = exp ((z * Complex.I) • G) * X * exp (-((z * Complex.I) • G)).
   Prove for every X and z, AnalyticAt ℂ (fun z => alpha(z,X)) z.
   Use the entire Banach-algebra exponential composed with continuous linear
   scalar multiplication, then analytic multiplication. All X in C are allowed;
   bounded G makes this entire, with no analytic-element hypothesis.
   Prove alpha((t:Complex),X) = seedRealTimeAut H hH beta t X.
   Native unitary conjugation has POSITIVE exp(i t G) convention; its star factor
   is exp(-i t G) by self-adjointness. Do not depend on unfinished motion claims.

3. Prove alpha(i*beta,X) = delta * X * delta⁻¹ and
   alpha(t+i*beta,X) = delta * alpha(t,X) * delta⁻¹.
   Commuting scalar multiples of G and exp_add_of_commute give the shift law.
   The sign is +i beta because (i beta)*i = -beta. The opposite imaginary shift
   gives inverse-density conjugation. Complex alpha is an algebraic inner
   automorphism, generally NOT a star automorphism off the real axis.

4. For arbitrary X,Y : C use the actual scalar function
   F(z) = phi (Y * alpha(z,X)). Prove it entire and continuous, with boundaries
   F(t) = phi (Y * seedRealTimeAut H hH beta t X),
   F(t+i*beta) = phi (seedRealTimeAut H hH beta t X * Y).
   The second equality uses the ALREADY PROVED concrete
   finiteSeed_representedVacuumTwistedCyclic, at alpha(t,X),Y, in reverse.
   No traciality, state faithfulness, or KMS premise is permitted in the final
   specialized result. A generic helper may accept twisted cyclicity only if
   this concrete application discharges it with the existing owner theorem.

These four steps are the narrow first theorem family: genuine complex-time
extension plus exact scalar boundary for the existing represented state.
They hold for every real beta. They do not yet assert a bounded-strip predicate.

## Separate bounded-strip obligation

For the conventional upper strip require beta > 0; beta = 0 is degenerate and
beta < 0 reverses orientation. Entire analyticity alone does not prove boundedness
on an unbounded horizontal strip. Derive it rather than assuming it:
write z=t+i*s, 0≤s≤beta, and use
alpha(z,X)=alpha(t,alpha(i*s,X)). Real-time star automorphisms are isometries.
The function s ↦ alpha(i*s,X) is continuous on the compact interval [0,beta],
so its norm has a finite bound M_X. Then
|F(z)| ≤ ‖phi‖ * ‖Y‖ * M_X uniformly in t.
This compact-interval argument avoids inventing an unverified exponential norm API.
After separately proving this bound, continuity on the closed strip and
holomorphy in its interior follow from the entire theorem. Only then may the
specific finite-seed system be called strip-KMS in the stated convention.
An optimal bound ‖X‖‖Y‖ is a further task, not needed for this boundedness contract.

## Inspected native references

- Canonical/FiniteSeedRepresentedKMS.lean: representedVacuumTwistedCyclic,
  representedVacuumTwistedCyclic_of_readback, seedDensityUnit,
  finiteSeedVacuum_algebraic_readback, finiteSeed_representedVacuumTwistedCyclic.
  SHA a464813d8111a734e7c8e5729af69492d7db63051cd15fef530aaa45edb33ec6.
- Canonical/FiniteSeedRepresentedRealTime.lean: matrixGenerator (124),
  matrixDensityUnit, matrixRealTimeAut (167), representedMatrixStageMap,
  seedDensityUnit_eq_stage_map, seedStageHom (253), representedDensityUnit,
  seedRealTimeAut (268), finiteSeed_realTime_state_invariant.
  SHA de19e22b0619c2d9a743dac42355971c4223c27bffeb41033b7ff1135862232e.
- Canonical/FilteredGNSBoundedGeneratorUnitaryFlow.lean:
  boundedGeneratorUnitary (76), cstar_selfAdjoint_expUnitary_add,
  boundedGeneratorClosureUnitaryFlow. Native bounded self-adjoint construction,
  not an unbounded Stone theorem.
  SHA 076d3351170168673fc22f70120cccc19a6e9ace4d16e3caa266cce6b798d489.
- Canonical/FiniteMatrixGibbsFunctional.lean: expWeight (37), gibbsDensity (39),
  gibbsDensityUnit. Weight is exp(-beta*r), not exp(+beta*r).
- Canonical/FilteredGNSVacuumReadback.lean: representedVacuumFunctional (61);
  Canonical/FilteredGNSVacuumState.lean: representedVacuumState (62).
- Canonical/FiniteCFCNormedExpGibbsBridge.lean (24-44) records CFC/readout
  equalities ONLY. It explicitly does not provide the desired series-exponential
  bridge on raw square matrices.
  SHA 5889db8b2de5757570f1c89940451442ddfb71c0d3e8e45f439ad4342b5bc356.
- Canonical/ModularFlowExponentialGenerator.lean (48,52): the existing
  complexExponentialConjugationPath has REAL time domain and a derivative at
  zero. Its name does not certify holomorphy in complex time.

## Inspected pinned Mathlib APIs

- Analysis/Normed/Algebra/Exponential.lean: NormedSpace.exp_analytic (498),
  exp_add_of_commute (520), map_exp (579); exp inverse identities in that owner.
  Analytic exponential uses completeness, already supplied by the actual C-star C.
- Analysis/Analytic/Linear.lean: ContinuousLinearMap.analyticAt (61).
- Analysis/Analytic/Constructions.lean: AnalyticAt.mul (650), scalar operations;
  analytic composition supplies the entire vector and scalar functions.
- Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean:
  StarAlgHomClass.map_cfc (462), StarAlgHom.map_cfc (487), with continuity
  and source/target CFC predicates explicitly required.
- Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean:
  CFC.real_exp_eq_normedSpace_exp (87).

This search is scoped to the actual finite-seed route and its analytic APIs;
it makes no repository-wide absence assertion about other KMS constructions.
No increasing Dirac/interacting limit, modular logarithm classification,
Tomita identification, state faithfulness or nontrivial-motion conclusion follows.
The fixed finite seed acts on the existing full represented closure; it is not
a construction of a growing Hamiltonian family. Separate independent AA and
locked kernel QA are required for future implementation.
