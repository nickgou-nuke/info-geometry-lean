# Weyl / Grand-Canonical / TKK / KKT Literature Context

Generated with the repository Alexandria pipeline on 2026-04-21.

## Pipeline Artifacts

- Seed list: `artifacts/alexandria/arxiv_seed_ids.txt`
- Fetch manifest: `artifacts/alexandria/weyl_grand_context/cache/MANIFEST.tsv`
- Semantic digest: `artifacts/alexandria/weyl_grand_context/digest/`
- Overlay summary: `artifacts/alexandria/weyl_grand_context/digest/overlay/summary.json`
- General retrieval: `artifacts/alexandria/weyl_grand_context/context_packet.json`
- TKK retrieval: `artifacts/alexandria/weyl_grand_context/tkk_context.json`
- KKT optimization retrieval: `artifacts/alexandria/weyl_grand_context/kkt_optimization_context.json`

The fetch script retrieved TeX sources for all listed arXiv IDs.

## Extracted Mathematical Claims

### Grand-Canonical Singular Ensembles

Primary source: `artifacts/alexandria/weyl_grand_context/cache/2603.20571.tex.md`

Extracted claims:

- A two-sector singular ensemble is described: sector `A` is canonical with fixed effective particle number, sector `B` is grand-canonical with fluctuating energy and particle number.
- Thermodynamic data are encoded by simple-pole singularities of a static lapse function.
- Inverse temperatures are extracted by contour integrals around the singularities.
- The grand-canonical sector yields the combination `β μ`, controlling the weight `exp (-β * (E - μ * N))`.
- The grand-canonical action has the affine form `β * (E - μ * N)`.
- The comparison section explicitly links redshifted chemical potential with Tolman-Klein equilibrium and the grand-canonical trace form.

Repo owner surfaces:

- `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`
- `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean`
- `lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`

Lean status:

- `SimplePoleResidueData.beta_eq_four_pi_residue`
- `SimplePoleResidueData.grandCanonicalSingularAction`
- `SimplePoleResidueData.grandCanonicalSingularAction_eq_canonical_sub_muN`
- `ResidueContourHolonomyData.grandCanonicalContourHolonomyAction_eq_canonical_sub_muN`
- `ThermodynamicGenerator.stateRelativeGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw_of_zeroChemicalPotential`

Boundary:

- Complex contour integration and analyticity hypotheses are not formalized. They are represented as explicit fields in the residue/holonomy interface.

### Weyl Gauge / Redshift / Boundary Weyl Structure

Primary sources:

- `artifacts/alexandria/weyl_grand_context/cache/2309.11372.tex.md`
- `artifacts/alexandria/weyl_grand_context/cache/2411.12513.tex.md`

Extracted claims:

- Weyl conformal geometry is used as a gauge theory of local scale invariance.
- Weyl-covariant differential operators and curvature-like readouts are expressed in a gauge-covariant form.
- In AdS boundary geometry, Weyl rescalings contribute to boundary charges, Weyl anomalies, and stress-tensor Ward identities.
- Tolman-Klein equilibrium is represented by redshift-invariant temperature and chemical-potential products.

Repo owner surfaces:

- `lean/InfoGeometry/Canonical/WeylTransport.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`
- `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`

Lean status:

- `WeylGaugeField.generatedAlong`
- `WeylGaugeField.covariantGeneratedFlow`
- `WeylGaugeField.respondCovariantFlow_transform_eq`
- `TolmanKleinRedshiftData.temperatureRedshiftInvariant`
- `TolmanKleinRedshiftData.chemicalPotentialRedshiftInvariant`
- `WeylGaugeCovariantInterface.curvature_transform_eq`

Boundary:

- Full Weyl geometry over smooth manifolds is not claimed here. The repository owns a transport/gauge-covariance interface.

### TKK / Jordan / Three-Graded Closure

Primary source: `artifacts/alexandria/weyl_grand_context/cache/1609.00271.tex.md`

Extracted claims:

- The paper compares Tits, Kantor, and Koecher constructions associated to Jordan superalgebras.
- It distinguishes multiple definitions of structure algebra.
- For TKK-style constructions, the usable formal layer is the three-graded closure pattern with `g_-`, `g_0`, and `g_+`.
- The mixed bracket `g_+ × g_-` closes in the grade-zero part.

Repo owner surfaces:

- `lean/InfoGeometry/Jordan/Core.lean`
- `lean/InfoGeometry/Canonical/KKTCore.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`

Lean status:

- `InfoGeometry.Jordan.JordanAlgebra`
- `KKTCore.IsGZero`
- `KKTCore.IsGOne`
- `KKTCore.IsGNegOne`
- `TKKThreeGradedClosure.bracketPlusMinusMemZero`
- `TKKThreeGradedClosure.bracketZeroPlusMemPlus`
- `TKKThreeGradedClosure.bracketZeroMinusMemMinus`
- `TKKThreeGradedClosure.bracketZeroZeroMemZero`

Boundary:

- The repo does not identify `KKTCore` with Karush-Kuhn-Tucker optimization. `KKTCore` is a split-operator/chiral grading surface.
- Full Tits-Kantor-Koecher construction from Jordan superalgebras remains external proof debt unless a concrete construction is added.

### Karush-Kuhn-Tucker Optimization

Primary source: `artifacts/alexandria/weyl_grand_context/cache/2210.15393.tex.md`

Extracted claims:

- Data-driven inverse optimization can be formulated as a bilevel program and then transformed into a single-level optimization problem using Karush-Kuhn-Tucker optimality conditions.
- The relevant optimization packet consists of objective/constraint data, primal feasibility, dual feasibility, stationarity, and complementary slackness.

Repo owner surfaces:

- `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`

Lean status:

- `KKTEntropyStationarityShadow` already exists as the Souriau/KKT finite admissibility packet.

Boundary:

- This is distinct from `lean/InfoGeometry/Canonical/KKTCore.lean`.
- No theorem should conflate Karush-Kuhn-Tucker conditions with the repo's chiral grading `KKTCore` without an explicit bridge structure.

## Arango / Repo Corridor

Earlier Arango graph descent for the combined query
`Weyl gauge redshift Tolman Klein grand canonical ensemble chemical potential particle number TKK Tits Kantor Koecher Jordan conformal KKT Karush Kuhn Tucker thermodynamic optimization Massieu partition`
identified the strongest live repo corridor around:

- `InfoGeometry.Canonical.ThermodynamicGenerator.stateRelativeGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw_of_zeroChemicalPotential`
- `InfoGeometry.Canonical.ThermodynamicGenerator.stateRelativeGrandCanonicalMassieuExpectation_eq_value_of_zeroChemicalPotential`
- `WeylGaugeField.respondCovariantFlow_transform_eq`
- `WeylGaugeField.generatedAlong`
- `WeylGaugeField.covariantGeneratedFlow_flowOf_apply`

This confirms that the proof-authority lane is grand-canonical Massieu transport plus Weyl gauge transport, not an ad hoc prose synthesis.

## Next Formal Move

The lowest-risk Lean extension is to add an explicit Karush-Kuhn-Tucker optimization packet to the literature bridge, or to import/reuse the existing `KKTEntropyStationarityShadow` from `SouriauLieThermoKKTBridge.lean`.

Recommended theorem-surface additions:

- `KarushKuhnTuckerThermodynamicData`
- `KarushKuhnTuckerThermodynamicData.packet`
- `LiteratureWeylGrandCanonicalTKKBridge` optionally extended with a KKT optimization field, keeping it separate from `KKTCore`

Do not claim:

- Full analytic contour integration.
- Full smooth Weyl manifold theory.
- Full TKK construction from Jordan superalgebras.
- Full thermodynamic KKT derivation from entropy maximization.

These remain explicit closure debt unless promoted into concrete Lean owners.
