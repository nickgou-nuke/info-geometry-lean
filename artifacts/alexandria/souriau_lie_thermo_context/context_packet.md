# Souriau Lie Thermodynamics Literature Context Packet

Date: 2026-04-21

Scope: build a repo-grounded theorem context for the Souriau Lie
thermodynamics prose: coadjoint moment map, geometric temperature, Massieu
potential, Fisher/BKM Hessian, Fenchel-Legendre duality, Onsager entropy
production, metriplectic split, and Karush-Kuhn-Tucker stationarity.

## Source Acquisition

Downloaded and extracted locally:

- `2104.12621`: arXiv source via `tools/alexandria/fetch_arxiv_corpus.py`.
- `2109.12806`: arXiv source via `tools/alexandria/fetch_arxiv_corpus.py`.
- `PMC7761515`: HTML and text extraction.
- `PHY2024-0346.pdf`: ATINER PDF and `pdftotext` extraction.
- `or706-LF-transform-1.pdf`: NCSU Legendre-Fenchel notes and
  `pdftotext` extraction.

Attempted but blocked by local HTTP 403:

- MDPI Entropy/Nanomaterials pages in the pasted bibliography.
- AIP JCP PDF.

The blocked sources are not treated as local evidence.  They can be cited only
as external references if separately opened through a browser/web tool.

Artifacts:

- Raw cache: `artifacts/alexandria/souriau_lie_thermo_context/cache`
- Alexandria digest: `artifacts/alexandria/souriau_lie_thermo_context/digest`
- Retrieval outputs: `artifacts/alexandria/souriau_lie_thermo_context/retrieval`

## Extracted Mathematical Claims

Claim A: Massieu/log-partition.

- Literature form: `Z(beta) = integral exp(-<J,beta>)`,
  `Phi(beta) = log Z(beta)`.
- Lean owner: `SouriauThermodynamics.souriauMassieuPotential_eq_log_partition`.
- Translator theorem:
  `SouriauTheoremTranslatorPacket.claimA_massieu_eq_log_partition`.

Claim B: first derivatives give thermodynamic moments.

- Literature form: first variation of `Phi` returns the mean moment-map
  readout, with sign depending on convention.
- Lean owner:
  `souriau_beta_conjugate_shifted_readout`,
  `souriau_mu_conjugate_number_readout`.
- Translator theorem:
  `claimB_firstDerivatives_eq_moments`.

Claim C: Hessian/Fisher/covariance.

- Literature form: second variation of `Phi` is Fisher information and equals
  covariance of moment-map readouts.
- Lean owner:
  `souriauFisher_betaBeta_eq_varianceShift`,
  `souriauFisher_muMu_eq_beta_sq_varianceNumber`,
  `souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance`,
  `souriauFisherResponseMatrix_symmetric`.
- Translator theorem:
  `claimC_hessian_eq_fisher_eq_covariance`.

Claim D: Fenchel-Legendre duality and inverse Hessian.

- Literature form: entropy is Fenchel/Legendre dual to Massieu; under smooth
  nondegeneracy, entropy Hessian is inverse Fisher Hessian.
- Finite Lean owner:
  `SouriauFenchelOnsagerBridge.SouriauFenchelContext`.
- Smooth inverse owner:
  `Geometry.LegendreHessianInverse.LegendreHessianInverseContext`.
- Infinite/coadjoint theorem surface:
  `SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext`.
- Translator theorems:
  `claimD_fenchelLegendre_contact_packet`,
  `claimD_scalarLegendre_inverseHessian_eq_inv_fisher`,
  `claimCD_fullCoadjointOrbit_hessian_packet`.

Claim E: Onsager/metriplectic entropy production.

- Literature form: `J = L X`, `sigma = X^T L X >= 0`; reversible/Casimir
  channel contributes zero entropy production.
- Finite Lean owner:
  `souriauEntropyProduction_nonneg_of_positiveSemidefinite`.
- Operatorial Lean owner:
  `SouriauKreinMetriplecticContext`.
- Infinite/coadjoint owner:
  `InfiniteCoadjointOrbitMetriplecticContext`.
- Translator theorem:
  `claimE_entropyProduction_nonneg_of_PSD` and
  `claimCDE_fullCoadjointOrbit_hessian_metriplectic_packet`.

Claim M: symplectic-leaf/Casimir and transverse Onsager split.

- Literature form: entropy is Casimir-invariant on symplectic/coadjoint
  leaves; transverse metric/Onsager motion produces nonnegative entropy.
- Lean owner:
  `InfiniteCoadjointOrbitMetriplecticContext`,
  `full_coadjoint_orbit_metriplectic_theorem`.
- Translator theorem:
  `claimM_coadjointLeaf_Casimir_transverseOnsager_packet`.
- Boundary: the theorem assumes an instantiated coadjoint-orbit metriplectic
  context.  It does not construct a symplectic foliation from a concrete
  infinite-dimensional manifold.

Claim K: Karush-Kuhn-Tucker stationarity.

- Literature form: equilibrium under constraints requires admissibility,
  stationarity, complementarity, and finite partition/admissible domain gates.
- Lean owner:
  `SouriauLieThermoKKTBridge.KKTEntropyStationarityShadow`.
- Translator theorem added in this pass:
  `claimK_kktEntropyStationarity_packet`.
- Combined finite theorem added in this pass:
  `structuredSouriauKKTTranslatorPacket`.

Claim W: representation weight lift.

- Literature form: representation weights encode conserved readouts and, in
  conformal/Weyl language, scaling charges.
- Lean owner:
  `SouriauDensityWeightContext.representationWeight`,
  `densityWeight_eq_numberWeight`,
  `liftedTransportGenerator_eq_souriau_add_number_weighted_dilationOperator`.
- Translator theorem:
  `claimW_representationWeight_lifts_to_densityTransport`.
- Boundary: this lifts only the finite number/charge component into the
  doubled-carrier density/dilation lane.  It does not identify all
  representation weights with an operator spectrum.

Claim S: super-coadjoint stress/supercurrent readouts.

- Literature form: stress tensor and supercurrent are projections of a single
  moment-map/coadjoint object.
- Lean owner:
  `SuperCoadjointMomentMapData`.
- Translator theorem:
  `claimS_superCoadjoint_stress_supercurrent_readouts`.
- Boundary: concrete stress tensor construction is still model data.

Claim T: conformal TKK/Jordan-Lie closure.

- Literature form: the conformal algebra can be organized by TKK/Jordan-Lie
  structure.
- Lean owner:
  `SplitCl44TKKJordanLiePacket`,
  `ConformalWeylTKKKKTJordanLieContext`.
- Translator theorem:
  `claimT_splitCl44_TKK_JordanLie_packet`.
- Boundary: this is not a full `Spin(4,4)` triality theorem, split-octonion
  classification theorem, or unconditional TKK construction.  It projects the
  explicit operatorial closure packet already present in the repo.

## Arango/DGA Navigation Result

Arango faithful retrieval was run with the query:

`Souriau coadjoint moment map geometric temperature geometric heat Casimir entropy Fisher Hessian Massieu Legendre Onsager metriplectic KKT Fenchel`

Strongest live corridor:

- `InfoGeometry.Canonical.ThermodynamicGenerator`
- Key theorem:
  `isPotentialKillingOperator_iff_isThermodynamicReadoutStationary`
- Layer: `L4_ModularTransport`

DGA around this owner showed a small downstream basin and no cyclic residue in
the quotient graph.  This is navigation only.  Proof authority remains with
the Lean owner files listed above.

## Formal Construction Plan

1. Keep finite Souriau thermodynamics in
   `Canonical/SouriauThermodynamics.lean`.
2. Keep finite Fenchel/Onsager contact in
   `Canonical/SouriauFenchelOnsagerBridge.lean`.
3. Keep KKT as explicit optimization hypotheses in
   `Canonical/SouriauLieThermoKKTBridge.lean`.
4. Expose multilingual theorem-factory claims in
   `Canonical/SouriauTheoremTranslatorPacket.lean`.
5. Use `Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean` only for the
   full infinite/coadjoint theorem surface, with analytic obligations as
   explicit context fields.

No theorem in this packet claims that external prose, Arango proximity, or an
Alexandria retrieval hit is a proof.
