# Actual represented Gibbs density exponential — sandbox contract

Author: Popper. Source-only, uncompiled; independent semantic AA and serialized
QA are required. No live owner, dependency, budget or transparency changes.

Source: FiniteSeedRepresentedDensityExponential20261024.lean.
Four named theorems, no new mathematical definitions/carriers:

1. For an actual star algebra hom f from finite complex matrices to any CStarAlgebra A,
   map_gibbsDensity_eq_exp proves f(gibbsDensity H hH beta)=exp((-beta) • f H).
   The finite Hermitian CFC is identified using hH.cfc_eq. StarAlgHom.map_cfc
   transports it, with continuity derived by the finite-dimensional linear-map
   theorem. cfc_comp_const_mul and CFC.real_exp_eq_normedSpace_exp finish inside A.
   A genuine target C-star norm is used; NO NormedRing instance is fabricated on
   raw Matrix. Self-adjointness of f H and its real multiple is derived.
2. map_gibbsDensityUnit_inv_eq_exp identifies the inverse of the mapped EXISTING
   gibbsDensityUnit with exp(beta • f H). Units.inv_eq_of_mul_eq_one_right and
   NormedSpace.exp_add_of_commute establish inverse uniqueness. The density
   identity is proved by theorem 1, not assumed.
3–4. Specialize exactly to seedStageHom H hH beta and representedDensityUnit
   H hH beta, on representedCStarClosure CStarMatrixStage
   cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH beta).
   The generator is J H, definitionally the value of native seedGenerator.
   There is no substitute map, state, density or supplied equality premise.

Premises: finite decidable nonempty matrix index for the generic results;
Hermitian H; arbitrary real beta. Concrete MatrixStage k is inherently nonempty.
There is no beta positivity, injectivity, state faithfulness, traciality,
normalization or analytic-element hypothesis. The unit is unnormalized; no
partition factor belongs in these exponential identities.

Native sources reused:
- Canonical/FiniteMatrixGibbsFunctional.lean: gibbsDensity, gibbsDensityUnit,
  gibbsDensityUnit_coe; the weight is Real.exp(-beta*r).
- Canonical/FiniteSeedRepresentedRealTime.lean: seedStageHom,
  representedDensityUnit, matrixDensityUnit, seedGenerator.
  Read baseline SHA de19e22b0619c2d9a743dac42355971c4223c27bffeb41033b7ff1135862232e.
- Canonical/FiniteMatrixGibbsNontracial.lean uses the same finite-dimensional
  continuity route for StarAlgHom.map_cfc. No raw-matrix normed-ring assumption.
- Mathlib CFC Unique: StarAlgHom.map_cfc; CFC Unital: cfc_comp_const_mul;
  ExpLog.Basic: CFC.real_exp_eq_normedSpace_exp; Exponential: exp_add_of_commute;
  Algebra/Group/Units/Basic: Units.inv_eq_of_mul_eq_one_right.

Local CFC and concrete stage family instances are actual native instances.
No budget overrides are introduced; elaboration of the dependent concrete
specialization remains for QA. This candidate does not prove a complex-time
extension, a strip bound, analytic KMS, or growing-generator compatibility.
The separate raw-colimit-unit alignment remains in the existing seed owner;
this candidate addresses only step 1 on the actual represented density.
