# Electric and magnetic flux: existing codebase map

Classification: **documentation-only source inventory**. Review date:
2026-11-20. Main revision inspected:
[`586c14bc9fb94eb09b56f7dc850d9d5297269f91`](https://github.com/nickgou-nuke/info-geometry-lean/commit/586c14bc9fb94eb09b56f7dc850d9d5297269f91).

This map records the source review requested after the binary-flux work. It
distinguishes constructed objects, consequences of supplied hypotheses, and
the smallest paper-specific connections not found in the inspected corridor.
It does not promote every named owner to freshly compiled status.

## Source and publication boundary

The source is G. 't Hooft, *A property of electric and magnetic flux in
non-Abelian gauge theories*, Nuclear Physics B153 (1979), 141–160,
[doi:10.1016/0550-3213(79)90595-9](https://doi.org/10.1016/0550-3213(79)90595-9).
The subsequently supplied `14317.pdf` is the same article with a Utrecht
repository cover sheet: 21 PDF pages, with printed pages 148–149 on PDF pages
9–10. Its SHA-256 is
`9769ee5cd27a9b65d52d3458fbff4bc7d1ef116c83999d835ee1e4e4e927230b`.
The original 20-page scan and its different checksum remain identified in the
[binary theorem contract](BINARY_FLUX_DUALITY_CONTRACT.md).

[PR #416](https://github.com/nickgou-nuke/info-geometry-lean/pull/416) was open,
draft, and unmerged at this review. Its initial published implementation
commit was `9db2547bcf3c424044c5e528b9e1d8911f0e6f3a`. The two binary-flux
owners are additions over the main revision above. All other canonical owners
in this map were already on that main revision. The documentation follow-up
does not change their Lean source or dependency pins.

## 1. Constructed finite representation and character machinery

### General finite-group character projection

[FiniteGroupCharacterProjection](../lean/InfoGeometry/Algebra/FiniteGroupCharacterProjection.lean)
already constructs the single-character projector through Mathlib's
`Representation.averageMap`. Its inputs are a native representation
`ρ : Representation k G V`, a unit-valued scalar character `χ : G →* kˣ`,
`[CommRing k]`, a finite group `G`, and invertibility of its order in `k`.
The group need not be abelian and the module need not be finite dimensional.

The inverse-character twist gives the normalized formula

\[
P_\chi v=|G|^{-1}\sum_{g\in G}\chi(g)^{-1}\rho(g)v.
\]

`projector_apply`, `projector_isProj`, `projector_idempotent`,
`range_projector`, and `projector_natural` derive the finite sum, projection,
range, and equivariant naturality. These are algebraic projections; no inner
product or self-adjointness hypothesis is supplied here.

An actual consumer is
[CharacterRelationQuotient](../lean/InfoGeometry/Algebra/CharacterRelationQuotient.lean):
`sectorQuotientEquiv` constructs compatibility between a character sector and a
stable relation quotient using the projector's naturality. This is a useful
existing connection for constraints and relations.

### Ordered operator Fourier and braiding algebra

| Canonical owner | Constructed content and declarations | Boundary |
|---|---|---|
| [FiniteGroupFourier](../lean/InfoGeometry/Algebra/FiniteGroupFourier.lean) | `finiteRepresentationTransform` uses `MonoidAlgebra.lift`; `_apply` evaluates the actual sum; `_convolution` preserves the ordered product in a possibly noncommutative algebra. | The inverse-argument convention uses `Aᵐᵒᵖ` and reverses product order. A complete irreducible dual or compact-group limit is not asserted. |
| [OperatorBraiding](../lean/InfoGeometry/Weyl/OperatorBraiding.lean) | `clockUnit` and `shiftUnit` are units in the matrix ring; `clockUnit_shiftUnit_commutator` identifies their group commutator with diagonal plaquette holonomy. `braidingHolonomy_gauge` derives gauge covariance. | Link units and the permutation are supplied. Spatial linking numbers and disorder operators are not constructed. |
| [OperatorBraidingExamples](../lean/InfoGeometry/Weyl/OperatorBraidingExamples.lean) | Explicit coefficients in `M₂(ℤ)` yield a holonomy that is neither scalar nor central. | A concrete finite operator witness. |
| [FiniteHeisenbergGroup](../lean/InfoGeometry/Canonical/FiniteHeisenbergGroup.lean) | Native group law and `finiteHeisenberg_group_commutator`, with central coordinate `x₁ y₂ − y₁ x₂`. | The coordinate cardinality lives in the core owner; the group wrapper does not itself install every finiteness interface. |
| [ProjectiveMultiplierCocycle](../lean/InfoGeometry/Canonical/ProjectiveMultiplierCocycle.lean) | `multiplier_cocycle` derives the scalar 2-cocycle equation from associativity and scalar cancellation. | The nonzero projective lift and its multiplication law are supplied, and the scalar multiplier is complex. |

For noncentral braiding, `OperatorBraiding.braided_power_law` derives

\[
zx=qxz\quad\Longrightarrow\quad zx^n=c_nx^nz,
\]

where `braidingPowerCocycle` is an ordered conjugation cocycle.
`braidingPowerCocycle_eq_one_of_pow_eq_one` shows that this accumulated cocycle
closes when `x^N = 1`. It does not infer `q^N = 1` for a noncentral one-step
factor.

[YangMillsTHooftWilsonBraiding](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/YangMillsTHooftWilsonBraiding.lean)
contains further star-ring identities from `N * N = 0` and
`N * star N * N = N`. The sign relation
`Z_center_braid_U_plus_off` concerns the off-diagonal corner of the link.
Conjugation of the full unipotent `1 + N` gives `1 - N`; it does not give a
minus sign on the entire unipotent. These hypotheses allow `N = 0`, so a
nonzero physical loop must be established separately.

## 2. Real binary characters and finite partition functions

| Canonical owner | Actual result | Carrier and supplied inputs |
|---|---|---|
| [WalshCharacterGeometry](../lean/InfoGeometry/LLM/WalshCharacterGeometry.lean) | `walshCharacter_orthogonality`, `walshMatrix_mul_transpose`, and `walshMatrix_isHadamard`. | Native real `AddChar`s on `ι → ZMod 2`, for finite `ι`. |
| [V4GroupFourierTransform](../lean/InfoGeometry/Canonical/V4GroupFourierTransform.lean) | Four real characters and `v4Fourier_inversion` with factor `1/4`. | The Klein four-group. |
| [V4CharacterGibbsPoUBridge](../lean/InfoGeometry/Canonical/V4CharacterGibbsPoUBridge.lean) | Constructed character projectors, product/idempotence/completeness, and finite Boltzmann/Gibbs character expansions. | The regular function carrier `V4Group → ℝ`. |
| [V4WeylGibbsOperatorBridge](../lean/InfoGeometry/Canonical/V4WeylGibbsOperatorBridge.lean) | `cayleyV4Representation`, `v4HaarAverage_eq_invariantProjector`, and `operatorProjector_mul`. | A concrete real coordinate representation. `gibbsOperator` is a probability-weighted mixture of its projectors when all gauge weights are positive, as required by `probability_pos` and `probability_sum_one`. |

The strongest inspected finite partition connection is
[PeirceV4GrandCanonicalFourierBridge](../lean/InfoGeometry/Canonical/PeirceV4GrandCanonicalFourierBridge.lean).
For a finite state space, energy/number observables, and supplied
`grade : α → V4Group`, it constructs

\[
Z_g=\sum_{\operatorname{grade}(x)=g}e^{-\beta(E_x-\mu N_x)}
\]

and proves both the twisted state-sum formula and its inverse:

\[
\widetilde Z_k=\sum_x\chi_k(\operatorname{grade}(x))
 e^{-\beta(E_x-\mu N_x)},\qquad
Z_g=\frac14\sum_k\chi_k(g)\widetilde Z_k.
\]

The declarations are `v4TwistedPartition_eq_state_sum` and
`v4Fourier_sector_inversion`. An empty grading fiber can have zero partition;
a nontrivial character sum is signed. The grading is not derived from gauge
twists in this owner.

Inspected consumers include
[SouriauChernFourierCharpolyCyclotomicPoset](../src/InfoGeometry/Canonical/SouriauChernFourierCharpolyCyclotomicPoset.lean),
`stage_S5_lie_group_fourier_character_and_v4_grand_canonical_inversion`, and
[SupergradedMoebiusTetraktysKleinVandermondeColorPoset](../src/InfoGeometry/Canonical/SupergradedMoebiusTetraktysKleinVandermondeColorPoset.lean),
`stage_V4_cyclotomic_parafermion_mobius_witten_and_v4_fourier`. They package
existing inversion results with other statements. Their conjunctions do not
construct a map from gauge configurations into physical flux sectors.

Parameter conventions also need an explicit map: the `Thermo.weight` used by
the concrete V4 Gibbs operator has exponent `-E / β`, whereas the
grand-canonical and finite plaquette owners use `-β * E`. The shared parameter
name does not identify the two conventions.

## 3. Constructed gauge, bundle, and classical analytic owners

| Canonical owner | Substantive source content | Scope |
|---|---|---|
| [DerivationDifferentialForms](../lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean) | Native Chevalley–Eilenberg curvature and `connectionCurvature_bianchi`. | Derivation-based noncommutative differential calculus. |
| [DerivationGaugeTransport](../lean/InfoGeometry/OperatorAlgebra/DerivationGaugeTransport.lean) | `fundamentalCovariantDerivative_commutator` and `connectionCurvature_gaugeOneForm`. | Exact curvature covariance in an arbitrary algebra. The faithful regular-module calculation retains central curvature. |
| [DerivationMatrixEnergy](../lean/InfoGeometry/OperatorAlgebra/DerivationMatrixEnergy.lean) | Positive `Re tr(Xᴴ X)` energy, zero detection, and `matrixCurvatureEnergy_gaugeOneForm`. | Real or complex matrices (`RCLike`); a finite supplied frame of directions. |
| [SmoothPrincipalCartanBundleClosure](../lean/InfoGeometry/Canonical/SmoothPrincipalCartanBundleClosure.lean) | Smooth principal trivializations, local sections, derived `principalTransition_cocycle`, and concrete real inhabitants. | General principal-bundle infrastructure. |
| [DoubledMinkowskiManifoldYangMillsPDE](../lean/InfoGeometry/Lie/DoubledMinkowskiManifoldYangMillsPDE.lean) | Matrix-valued differential forms, `bianchi_identity_ymCurvature`, Hodge operators, and an explicit self-dual solution with nonzero curvature. | Classical equations on a concrete `M₄(ℂ)`/chiral carrier with real differential calculus. |
| [DoubledMinkowskiLatticeContinuumLimit](../lean/InfoGeometry/Lie/DoubledMinkowskiLatticeContinuumLimit.lean) | `tendsto_latticeCovariantDiff`, `tendsto_wilsonPlaquette_curvature`, and `tendsto_wilsonPlaquetteAction`. | Classical local small-mesh limits; the curvature/action limits require `C²` regularity. |

The local plaquette result establishes `(U_square - 1) / a² → F` for
matrix-exponential links. This is an analytic limit already present in the
codebase. It does not construct a quantum Euclidean measure, a thermodynamic
limit, or the paper's center-twisted torus.

### A concrete finite gauge Gibbs model

[FinitePlaquette](../lean/InfoGeometry/LatticeGauge/FinitePlaquette.lean)
constructs group-valued links, their local gauge action, and ordered plaquette
holonomy. `plaquetteHolonomy_gauge_covariant` proves conjugation covariance.
Its action is the sum of zero/one costs for nonidentity plaquette holonomy.

With finite edges, faces, and gauge group,
[FiniteGibbsModel](../lean/InfoGeometry/LatticeGauge/FiniteGibbsModel.lean)
constructs the normalized Boltzmann distribution and proves partition
positivity, positivity of each weight, normalization, and gauge invariance.
The action is not a trace-based SU(N) Wilson action.

Its downstream
[FiniteResamplingDynamics](../lean/InfoGeometry/LatticeGauge/FiniteResamplingDynamics.lean)
proves detailed balance and a spectrum contained in `{0, 1}` for the
complete-resampling operator `H = I - E_π`, with the stated nontriviality
conditions for the full spectral statement. This is not a spectral-gap theorem
for local gauge dynamics or a continuum Yang–Mills Hamiltonian.

No consumer connecting this plaquette Gibbs construction to the V4 physical
flux grading or 't Hooft twisted partition table was found in the bounded
import/consumer corridor inspected for this review.

## 4. The paper-specific binary addition in PR #416

[BinaryFluxProjectors](../lean/InfoGeometry/Algebra/BinaryFluxProjectors.lean)
reuses `FiniteGroupFourier` and `WalshCharacterGeometry`. For a representation
`Multiplicative (ι → ZMod 2) →* A` into an arbitrary real algebra, it derives
the complete explicit binary family, including

\[
P_eP_f=\delta_{ef}P_e,\qquad\sum_eP_e=1.
\]

It also derives ordered charge transport from supplied charge covariance and
finite-sum measurement through a real linear functional. The three-component
projector has eight terms and normalization `1/8`. Algebraic orthogonality does
not assert self-adjointness or nonzero occupation of every sector.

[BinaryFluxDuality](../lean/InfoGeometry/Algebra/BinaryFluxDuality.lean)
constructs, for two transverse binary coordinates,

\[
E(W)=\tfrac14HW,\qquad D(Z)=\tfrac14HZ^{\mathsf T}H.
\]

`fluxDuality_involutive` and `fluxDualityEquiv` establish an actual real linear
involution/equivalence. `electricTransform_eq_fluxDuality_of_transpose` derives
`E(W) = D(E(W'))` from `W = W'.transpose`.
`projected_electricTransform_eq_fluxDuality` retains the longitudinal electric
Fourier projection. The transverse sum has sixteen terms and normalization
`1/4`; fixing a longitudinal twist coordinate would be a different operation.

The physical table covariance is a premise. The finite duality equation is
derived from it through the constructed transform and inversion.

## 5. Interfaces and names requiring a narrower reading

| Owner | Actual assumption boundary |
|---|---|
| [KapustinWittenDuality](../lean/InfoGeometry/OperatorAlgebra/KapustinWittenDuality.lean) | `SDualityDatum` supplies the Wilson/'t Hooft readout equality; later results transport conditions across it. |
| [CyclotomicProjectorReadout](../lean/InfoGeometry/Canonical/CyclotomicProjectorReadout.lean) | `FourierCyclotomicReadout` stores projector laws and eigenrelations as fields. Its reconstruction consequence is valid, but those fields are not constructed there. |
| [GaugeGroups](../lean/InfoGeometry/Canonical/GaugeGroups.lean) | `SUN.toMatrix` lacks homomorphism and faithfulness laws; `PSUN` supplies a fiber-relation contract. These structures do not construct the intended quotient group and its torus bundles. This observation is specific to these structures. |
| [WilsonHooftDefects](../lean/InfoGeometry/Topological/WilsonHooftDefects.lean) | The defined defects are scalar cosine and complex exponential functions. The commutation result is scalar commutativity. |
| [SmithHatIsingDuality](../lean/InfoGeometry/External/Auto/SmithHatIsingDuality.lean) | The two `kramers_wannier_*_duality` theorems return their supplied scalar equations; they do not derive lattice partition duality. |

For real general-N work, the existing
[CyclotomicUnitRepresentation](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CyclotomicUnitRepresentation.lean)
constructs `DihedralGroup 3 →* Bˣ` over an arbitrary ring from explicit Peirce
hypotheses. The
[LanguageSymmetryDihedral](../lean/InfoGeometry/LLM/LanguageSymmetryDihedral.lean)
owner has general-N real `2 × 2` matrix representations and Fourier blocks,
but takes `AddChar (ZMod N) ℂ` as input and uses `Complex.I` in its
paired-character intertwiner. Real output and a construction entirely over
real scalars are distinct properties. A cosine substitution does not preserve
individual general-N character sectors.

## 6. Source lanes and remaining connections

The search covered related names, definitions, hypotheses, proof bodies,
imports, and consumers in `lean/` and `src/`, plus relevant tool/index paths.
Generated graph or report artifacts served only as navigation. No external
reference checkout was promoted to a repository-owned proof.

The source lanes must be identified explicitly. For example,
`DerivationDifferentialForms` has additional arbitrary-degree material in
`lean/`; `YangMillsTHooftWilsonBraiding` has extra finite identities in `src/`.
`Weyl/OperatorBraiding` and `SmoothPrincipalCartanBundleClosure` have no matching
`src/` owner. The main links above identify the canonical files, and the two
consumer links deliberately identify `src/` files.

The smallest unresolved paper-specific connections found in this corridor are:

1. Construct the center-twisted torus gauge object and its electric/magnetic
   labels using actual groups, representations, and transition maps.
2. Construct its twisted partition table or appropriate trace/measure and
   connect its sector decomposition to the existing finite Fourier owners.
3. Prove the rotation/covariance identity for that object. The binary algebraic
   implication of this identity is already supplied by PR #416.
4. For general N, construct compatible real phase operators and prove the
   required character-sector compatibility and orthogonality.
5. Supply the physical asymptotic hypotheses and analytic limits for the
   paper's phase conclusions. Its assumed free-energy factorization is not a
   consequence of finite Fourier inversion.

This is a bounded reuse map, not a repository-wide nonexistence theorem.
No conceptual adjacency above is asserted to be an implemented map.

## Validation scope

This inventory changes documentation only. Source paths, named declarations,
and the publication distinction were reviewed against the stated revisions;
no new Lean theorem or fresh broad compilation is claimed.

The unchanged binary owners have their own
[focused validation record](BINARY_FLUX_DUALITY_VALIDATION.md): six modules
compiled and 68 owned declarations passed the native axiom audit under the
pinned environment. That record also identifies the blocked root integration.
The prior focused result does not certify every owner listed in this map, and
publication of this documentation does not resolve the root-package blocker.
