# Exhaustive Upstream PR Reconciliation & Asset Inventory

## 1. Global Verification Summary

- **Total Open PRs Audited**: 104
- **Total Distinct Missing Files in `main`**: 177
  - **Unique `.lean` Files**: 55
  - **Unique `.md` Doc Files**: 33
  - **Unique Other Files (scripts, json, reports)**: 89

### PR Classification Breakdown
- **All Files Exist in `main` (with modifications/evolution)**: 66 PRs
- **Partial / Mixed Files (some exist in `main`, some are unique)**: 36 PRs
- **All Files Missing from `main` (brand new topic packages)**: 2 PRs

---

## 2. Exhaustive Roster of the 55 Unique Missing Lean Files

| # | Relative Path | Contributing PR(s) |
| :-: | :--- | :--- |
| 1 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorBeerLambert.lean` | #169 |
| 2 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorDiskIntegral.lean` | #169 |
| 3 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorResponseAudit.lean` | #169 |
| 4 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorResponseBridgeAudit.lean` | #169 |
| 5 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorResponseCore.lean` | #169 |
| 6 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorResponseIntegral.lean` | #169 |
| 7 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorTransportKernel.lean` | #169 |
| 8 | `artifacts/formalization/detector_response_integral/lean/InfoGeometry/Nuclear/DetectorVolumeResponse.lean` | #169 |
| 9 | `external_refs/gift-framework-core/GIFT/Algebraic/Octonions.lean` | #88, #89, #90, #91, #92, #93 |
| 10 | `external_refs/gift-framework-core/lakefile.lean` | #88, #89, #90, #91, #92, #93 |
| 11 | `lean/InfoGeometry/Algebra/FourthRootPeirceProjectors.lean` | #165 |
| 12 | `lean/InfoGeometry/Analysis/ModifiedBesselOrderZero.lean` | #168 |
| 13 | `lean/InfoGeometry/Arithmetic/RiemannApolloniusCorrectedDiagnostics.lean` | #95, #97 |
| 14 | `lean/InfoGeometry/Canonical/ApolloniusLambdaDAGDiagnostics.lean` | #97 |
| 15 | `lean/InfoGeometry/Canonical/ApolloniusMasterPotentialDiagnostics.lean` | #97 |
| 16 | `lean/InfoGeometry/Canonical/ExteriorCyclotomicPeirceAudit.lean` | #165 |
| 17 | `lean/InfoGeometry/Canonical/OperatorCliffordWeylCurvatureCapstone.lean` | #120 |
| 18 | `lean/InfoGeometry/Canonical/OperatorOddCliffordPauliLubanskiBridge.lean` | #120 |
| 19 | `lean/InfoGeometry/Canonical/OperatorQuaternionicLiftCapstone.lean` | #120, #122 |
| 20 | `lean/InfoGeometry/Canonical/OperatorWeylChiralCurvatureBlocks.lean` | #120 |
| 21 | `lean/InfoGeometry/Canonical/OperatorWeylChiralCurvatureResidue.lean` | #120 |
| 22 | `lean/InfoGeometry/Canonical/QuaternionicOperatorComplexStructure.lean` | #120, #122 |
| 23 | `lean/InfoGeometry/Canonical/QuaternionicOperatorLiftCurvature.lean` | #120 |
| 24 | `lean/InfoGeometry/Canonical/SelfConcordantLogGeneratingLyapunovDiagnostics.lean` | #97 |
| 25 | `lean/InfoGeometry/Canonical/SplitG2AlbertJordanCompatibility.lean` | #124 |
| 26 | `lean/InfoGeometry/Canonical/WeylChiralHodgeCurvatureSplit.lean` | #120 |
| 27 | `lean/InfoGeometry/Categorical/LogJordanHadjiivanovBraidingBridge.lean` | #122 |
| 28 | `lean/InfoGeometry/Categorical/LogNilpotentPhysicalBraidedCategory.lean` | #122 |
| 29 | `lean/InfoGeometry/Categorical/LogNilpotentPhysicalBraiding.lean` | #120, #122 |
| 30 | `lean/InfoGeometry/Categorical/LogNilpotentPhysicalBraidingHexagon.lean` | #120, #122 |
| 31 | `lean/InfoGeometry/Clifford/ExteriorDegreePhaseFour.lean` | #165 |
| 32 | `lean/InfoGeometry/LLM/ContinuousMeanFieldClosure.lean` | #168 |
| 33 | `lean/InfoGeometry/LLM/SphericalVMFExponentialFamily.lean` | #168 |
| 34 | `lean/InfoGeometry/LLM/SphericalVMFFieldDerivatives.lean` | #168 |
| 35 | `lean/InfoGeometry/LLM/SphericalVMFNativeAudit.lean` | #168 |
| 36 | `lean/InfoGeometry/Nuclear/ConformalDetectorIntegral.lean` | #170 |
| 37 | `lean/InfoGeometry/Nuclear/ConformalDetectorIntegralAudit.lean` | #170 |
| 38 | `lean/InfoGeometry/Nuclear/FocalRapidity.lean` | #170 |
| 39 | `lean/InfoGeometry/Nuclear/FocalSechODE.lean` | #170 |
| 40 | `lean/InfoGeometry/OperatorAlgebra/Cl55FreudenthalZornGradeIntertwiner.lean` | #166 |
| 41 | `lean/InfoGeometry/OperatorAlgebra/Cl55FreudenthalZornLieRepresentation.lean` | #166 |
| 42 | `lean/InfoGeometry/OperatorAlgebra/Cl55FreudenthalZornRestrictedGradeMaps.lean` | #166 |
| 43 | `lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornAll.lean` | #166 |
| 44 | `lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornAudit.lean` | #166 |
| 45 | `lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornIntertwinerClosure.lean` | #166 |
| 46 | `lean/InfoGeometry/OperatorAlgebra/RealWeylAdjointSpinRepresentation.lean` | #166 |
| 47 | `lean/InfoGeometry/Sandbox/scratch_colim_test.lean` | #88, #89, #90, #91, #92, #93 |
| 48 | `lib/InfoGeometryCore/InfoGeometryCore/Basic.lean` | #88, #89, #90, #91, #92, #93 |
| 49 | `lib/InfoGeometryCore/lakefile.lean` | #88, #89, #90, #91, #92, #93 |
| 50 | `tests/GibbsReferenceGaugeAxiomAudit.lean` | #150, #155, #158, #163 |
| 51 | `tests/OperatorZornGaugeAxiomAudit.lean` | #146, #150, #155, #158, #163 |
| 52 | `tests/ProjectiveGraphZornBilayerAxiomAudit.lean` | #155, #158, #163 |
| 53 | `tests/ProjectiveZornAttentionAxiomAudit.lean` | #150, #155, #158, #163 |
| 54 | `tests/SplitAtomAxiomAudit.lean` | #139 |
| 55 | `tests/ZornRindlerAxiomAudit.lean` | #146, #150, #155, #158, #163 |

---

## 3. Complete Per-PR Classification Ledger (All 104 Open PRs)

| PR # | Classification | Total Files | Identical | Modified | Missing | Title |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| #63 | `PARTIAL_MIXED_FILES` | 2 | 0 | 1 | 1 | feat(g2): align finite roots with native nonzero indices |
| #64 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | feat(g2): add depth-safe flag factorization recursion |
| #65 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | Prove Fin189 Bruhat orbit membership from concrete witness data |
| #66 | `PARTIAL_MIXED_FILES` | 2 | 0 | 1 | 1 | Add the Topological Progress Principle for formal development |
| #67 | `PARTIAL_MIXED_FILES` | 2 | 0 | 1 | 1 | docs: establish Topological Progress Principle |
| #68 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | Close intrinsic G2 flag cardinality from native fiber transport |
| #69 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | feat(g2): isolate final residual readbacks for stabilizer closure |
| #70 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | feat(geometry): add trifactor readout contracts |
| #71 | `ALL_FILES_EXIST_BUT_MODIFIED` | 7 | 3 | 4 | 0 | feat(arithmetic): add directed prime cyclotomic Galois certificates |
| #72 | `ALL_FILES_EXIST_BUT_MODIFIED` | 3 | 0 | 3 | 0 | Add O(1) six-prime cyclotomic Galois tower certificates |
| #73 | `ALL_FILES_EXIST_BUT_MODIFIED` | 5 | 0 | 5 | 0 | Add native six-prime cyclotomic directed tower |
| #74 | `ALL_FILES_EXIST_BUT_MODIFIED` | 4 | 0 | 4 | 0 | Add generic graded Jacobi closure for Freudenthal tower |
| #75 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | feat(algebra): bridge eight circular chiral operators to Peirce basis |
| #76 | `ALL_FILES_EXIST_BUT_MODIFIED` | 2 | 0 | 2 | 0 | feat(clifford): add Cl55 dyadic Morita reconstruction |
| #77 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | feat(canonical): add Arnold–Kohno flat connection certificate |
| #78 | `ALL_FILES_EXIST_BUT_MODIFIED` | 3 | 0 | 3 | 0 | feat(clifford): formalize elliptic RoPE and split hyperbolic rotors |
| #79 | `ALL_FILES_EXIST_BUT_MODIFIED` | 5 | 0 | 5 | 0 | feat(nuclear): add finite Soloviev QPNM spectral closure |
| #81 | `ALL_FILES_EXIST_BUT_MODIFIED` | 4 | 0 | 4 | 0 | Prove positivity and strict definiteness of the full operator BKM form |
| #82 | `ALL_FILES_EXIST_BUT_MODIFIED` | 2 | 0 | 2 | 0 | Prove native BKM positivity by trace factorization |
| #83 | `ALL_FILES_EXIST_BUT_MODIFIED` | 3 | 0 | 3 | 0 | Prove strict BKM positivity |
| #84 | `ALL_FILES_EXIST_BUT_MODIFIED` | 2 | 0 | 2 | 0 | Bridge Hestenes–Krein curvature and canonical Pfaffian permutation matching |
| #85 | `ALL_FILES_EXIST_BUT_MODIFIED` | 4 | 0 | 4 | 0 | Add native Legendre differential and Hodge/BKM equivalence layers |
| #86 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | Formalize local nonlinear Zorn constraint reduction |
| #87 | `ALL_FILES_EXIST_BUT_MODIFIED` | 19 | 0 | 19 | 0 | Add Souriau–Klein operator orbit geometry bridge |
| #88 | `PARTIAL_MIXED_FILES` | 63 | 15 | 41 | 7 | Formalize finite mass-spectrometry grammar in native Mathlib |
| #89 | `PARTIAL_MIXED_FILES` | 75 | 19 | 49 | 7 | Formalize nuclear operator supergeometry in native Mathlib |
| #90 | `PARTIAL_MIXED_FILES` | 82 | 23 | 52 | 7 | Formalize nuclear Klein-equivariant parameter topology in native Mathlib |
| #91 | `PARTIAL_MIXED_FILES` | 80 | 21 | 52 | 7 | Connect nuclear quantum numbers to five-grade, Artin, and Galois symmetry corridors |
| #92 | `PARTIAL_MIXED_FILES` | 104 | 32 | 65 | 7 | Add theorem-safe QCD chiral, Zorn, and triality structural lane |
| #93 | `PARTIAL_MIXED_FILES` | 111 | 34 | 70 | 7 | Add real Hestenes-Krein color representation lane |
| #94 | `ALL_FILES_EXIST_BUT_MODIFIED` | 2 | 0 | 2 | 0 | Add categorical Mathlib Grothendieck completion natural isomorphism |
| #95 | `PARTIAL_MIXED_FILES` | 10 | 0 | 9 | 1 | Add theorem-safe Riemann zeta evidence corridor |
| #96 | `ALL_FILES_EXIST_BUT_MODIFIED` | 1 | 0 | 1 | 0 | Document Hilbert–Pólya spectral trust boundary |
| #97 | `PARTIAL_MIXED_FILES` | 19 | 0 | 15 | 4 | Add Apollonius lambda-DAG topological closure |
| #98 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Add native Apollonius Zorn potential bridge |
| #99 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Bridge native Cartan Souriau ensemble to dually-flat geometry |
| #100 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Bridge circular chiral rails to Fock operator-Zorn carrier |
| #101 | `ALL_FILES_EXIST_BUT_MODIFIED` | 356 | 243 | 113 | 0 | Unify exterior/CAR/Virasoro, chiral geometry, and Gibbs/BKM calculus |
| #102 | `ALL_FILES_EXIST_BUT_MODIFIED` | 339 | 243 | 96 | 0 | Categorical Hadjiivanov Hestenes–Krein braid descent |
| #103 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Formalize an exact one-mode CAR moment SDP |
| #104 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Reconcile CFC and Banach-exponential finite Gibbs states |
| #106 | `ALL_FILES_EXIST_BUT_MODIFIED` | 349 | 243 | 106 | 0 | Close the real Fréchet–Duhamel operator edge |
| #107 | `ALL_FILES_EXIST_BUT_MODIFIED` | 353 | 243 | 110 | 0 | Normalize faithful Gibbs powers and identify centered BKM response |
| #108 | `ALL_FILES_EXIST_BUT_MODIFIED` | 342 | 244 | 98 | 0 | Add native derivation forms, split-octonion operator covariance, and surprisal bridges |
| #109 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Formalize positional encodings as translation representations |
| #110 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 244 | 85 | 0 | Formalize the theorem-safe Riemann surprisal and flux audit |
| #111 | `ALL_FILES_EXIST_BUT_MODIFIED` | 348 | 244 | 104 | 0 | Add Apollonius logarithmic coordinates and Pauli lift |
| #112 | `ALL_FILES_EXIST_BUT_MODIFIED` | 354 | 243 | 111 | 0 | Package additive Gibbs Hessian as centered BKM covariance |
| #113 | `ALL_FILES_EXIST_BUT_MODIFIED` | 355 | 243 | 112 | 0 | Formalize the Logos-Partiture archetypal poset |
| #114 | `ALL_FILES_EXIST_BUT_MODIFIED` | 330 | 243 | 87 | 0 | Add concrete Cantor branch-exchange thermofield intertwiner |
| #115 | `ALL_FILES_EXIST_BUT_MODIFIED` | 356 | 243 | 113 | 0 | Formalize the corrected Krein para-Kähler twin-wave bridge |
| #116 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Add native Zorn to five-graded TKK socket |
| #117 | `ALL_FILES_EXIST_BUT_MODIFIED` | 333 | 243 | 90 | 0 | Formalize beta-reduction topology and thermodynamic traces |
| #118 | `ALL_FILES_EXIST_BUT_MODIFIED` | 330 | 243 | 87 | 0 | Add proof-relevant de Bruijn lambda topology |
| #119 | `ALL_FILES_EXIST_BUT_MODIFIED` | 332 | 243 | 89 | 0 | Add finite beta-reduction affinity and holonomy |
| #120 | `PARTIAL_MIXED_FILES` | 383 | 244 | 129 | 10 | Build LogCFT tensor-coherence DAG bridge |
| #121 | `ALL_FILES_EXIST_BUT_MODIFIED` | 338 | 243 | 95 | 0 | Add quaternionic Pauli–Dirac operator soldering bridge |
| #122 | `PARTIAL_MIXED_FILES` | 374 | 244 | 124 | 6 | Complete natural physical braiding on LogNilpotentModule |
| #123 | `ALL_FILES_EXIST_BUT_MODIFIED` | 330 | 243 | 87 | 0 | Derive the GUT weak angle from normalized SM gauge traces |
| #124 | `PARTIAL_MIXED_FILES` | 360 | 243 | 116 | 1 | Formalize H3 Kantor system, unconditional G2→F4 embedding, F4 constraint space, split TKK, E8 carrier, and Leech bridges |
| #125 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Formalize the four-Majorana Pfaffian matching spine |
| #126 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Add finite Berezinian super-barrier bridge |
| #127 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Formalize native gl(m\|n) graded supermatrix Lie spine |
| #128 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Close native split-octonion inner-derivation span at dimension 14 |
| #129 | `ALL_FILES_EXIST_BUT_MODIFIED` | 334 | 243 | 91 | 0 | Add exact 24-fold cyclotomic operator polynomial spine |
| #131 | `ALL_FILES_EXIST_BUT_MODIFIED` | 332 | 243 | 89 | 0 | Prove Peirce-0 quadratic homothety and injective conformal TKK spine |
| #133 | `ALL_FILES_EXIST_BUT_MODIFIED` | 348 | 243 | 105 | 0 | Add split spin-factor TKK conformal D6 bridge |
| #134 | `ALL_FILES_EXIST_BUT_MODIFIED` | 330 | 243 | 87 | 0 | Solder native F4 action certificate into the Tits E8 carrier |
| #135 | `ALL_FILES_EXIST_BUT_MODIFIED` | 335 | 243 | 92 | 0 | Close the algebraic soldering bridge from split G2 into H3Zorn/F4 |
| #136 | `ALL_FILES_EXIST_BUT_MODIFIED` | 408 | 244 | 164 | 0 | Formalize the bipolar cross-ratio logarithmic two-sheet operator spine |
| #137 | `ALL_FILES_EXIST_BUT_MODIFIED` | 329 | 243 | 86 | 0 | Prove operator-trace vanishing for all split-Albert derivations |
| #138 | `ALL_FILES_EXIST_BUT_MODIFIED` | 410 | 244 | 166 | 0 | Add native Apollonius operator connection and contour holonomy layer |
| #139 | `PARTIAL_MIXED_FILES` | 342 | 247 | 90 | 5 | Reconstruct split-atom geometry with native Clifford involutions, punctures and finite thermal proofs |
| #140 | `ALL_FILES_EXIST_BUT_MODIFIED` | 414 | 244 | 170 | 0 | Separate the Möbius coordinate, interval barrier, Berezinian, and spinorial descent |
| #141 | `PARTIAL_MIXED_FILES` | 419 | 244 | 172 | 3 | Reconstruct Cayley–Klein claims via native cochain twists and diagonal Berezinian |
| #142 | `ALL_FILES_EXIST_BUT_MODIFIED` | 334 | 245 | 89 | 0 | Formalize finite Penrose–Onsager–Yang condensation spectra and kernels |
| #143 | `PARTIAL_MIXED_FILES` | 341 | 243 | 92 | 6 | Formalize Penrose CCR triple, literal cross-product obstruction, and Witt composition completion |
| #144 | `ALL_FILES_EXIST_BUT_MODIFIED` | 333 | 246 | 87 | 0 | Formalize Zorn Peirce roots, the derivation Lie algebra, and CAR/CCR envelopes |
| #145 | `PARTIAL_MIXED_FILES` | 345 | 243 | 94 | 8 | Intertwine exterior CAR with circular Zorn operators and correct affine spin and Pin claims |
| #146 | `PARTIAL_MIXED_FILES` | 350 | 243 | 95 | 12 | Retain nonassociative operator-Zorn four-potential, curvature and gauge fields |
| #147 | `ALL_FILES_EXIST_BUT_MODIFIED` | 350 | 249 | 101 | 0 | Close the concrete nuclear five-grade CAR–phonon BdG–Soloviev lane |
| #148 | `PARTIAL_MIXED_FILES` | 346 | 245 | 97 | 4 | Formalize causal boundary conditioning, gauge routing, graph Dirac and graded G2 softmax |
| #149 | `PARTIAL_MIXED_FILES` | 345 | 243 | 101 | 1 | Reconstruct signed-network dynamics: cancellation, qubit Wigner kernel, and finite causal resolvent |
| #150 | `PARTIAL_MIXED_FILES` | 367 | 243 | 104 | 20 | Replace the false Freudenthal bracket with a faithful symplectic contact Lie representation |
| #151 | `ALL_FILES_EXIST_BUT_MODIFIED` | 336 | 243 | 93 | 0 | Close the finite nuclear five-grade CAR/BdG/CCR/Soloviev corridor |
| #152 | `ALL_FILES_EXIST_BUT_MODIFIED` | 359 | 249 | 110 | 0 | Replace the false Freudenthal bracket with a faithful symplectic contact Lie representation |
| #153 | `PARTIAL_MIXED_FILES` | 352 | 246 | 100 | 6 | Formalize generic two-boundary weak functionals and static Cheshire separation |
| #154 | `PARTIAL_MIXED_FILES` | 362 | 246 | 108 | 8 | Separate Cl55 occupation grades, boundary dyads, affine deck actions and log-ratio relaxation |
| #155 | `PARTIAL_MIXED_FILES` | 381 | 243 | 109 | 29 | Construct projective graph cycle decomposition and retain full Zorn bilayer defects |
| #156 | `PARTIAL_MIXED_FILES` | 394 | 249 | 125 | 20 | Construct the split O(5,5) contact multigrading and CAR–CCR representation |
| #157 | `PARTIAL_MIXED_FILES` | 369 | 247 | 114 | 8 | Lift two-boundary readouts to the full O(5,5) D5 multigrading |
| #158 | `PARTIAL_MIXED_FILES` | 381 | 243 | 109 | 29 | Construct projective graph cycle decomposition and retain nonassociative Zorn bilayer defects |
| #159 | `PARTIAL_MIXED_FILES` | 373 | 250 | 121 | 2 | Formalize complex Kramers symmetry, Klein deck quotient, and Pin(5,5) multigrading |
| #160 | `PARTIAL_MIXED_FILES` | 373 | 249 | 112 | 12 | Formalize polarized Zorn symmetries, fundamental metric symmetry, and boundary coefficients |
| #161 | `PARTIAL_MIXED_FILES` | 342 | 243 | 91 | 8 | Connect polarized 10D quadratic data to native Cl(5,5), spinors, and exterior Hodge readout |
| #162 | `PARTIAL_MIXED_FILES` | 387 | 250 | 133 | 4 | Formalize twin 4-operator Zorn, modular commutant, and Klein Dirac–Kähler blocks |
| #163 | `PARTIAL_MIXED_FILES` | 394 | 244 | 116 | 34 | Preserve full operator-Zorn twin fields and construct coefficient Fourier sectors |
| #164 | `ALL_FILES_EXIST_BUT_MODIFIED` | 339 | 249 | 90 | 0 | Construct fourth-root Fourier projectors and native exterior-degree Peirce bridges |
| #165 | `PARTIAL_MIXED_FILES` | 341 | 243 | 87 | 11 | Construct exterior degree-mod-four projectors and finite Peirce corners from native Clifford parity |
| #166 | `PARTIAL_MIXED_FILES` | 398 | 250 | 135 | 13 | Formalize Dirac–Hodge, real spin, and graded operator-Zorn intertwiners |
| #167 | `ALL_FILES_EXIST_BUT_MODIFIED` | 331 | 245 | 86 | 0 | Map the full mcbal comparison onto the native Sinkhorn–Hodge–IB corridor |
| #168 | `PARTIAL_MIXED_FILES` | 338 | 243 | 87 | 8 | Formalize spherical vMF measure, cumulant, and controlled closure calculus |
| #169 | `ALL_FILES_MISSING_FROM_MAIN` | 14 | 0 | 0 | 14 | Nuclear: actual detector response integral — isolated Lean candidate |
| #170 | `ALL_FILES_MISSING_FROM_MAIN` | 5 | 0 | 0 | 5 | Formalize prolate focal rapidity, flux ratio, and sech profile ODE |
