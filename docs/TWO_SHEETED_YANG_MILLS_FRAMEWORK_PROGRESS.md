# Two-Sheeted Yang–Mills Framework Progress

Status reviewed: 2026-11-15 against `abd5826b3676fab6231c66b646ec1cc5aeed6732` plus scoped working-tree kernel verification of `InfoGeometry.Foundations.InfoGeometryCoreLibrary` and `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All` (this scoped check covers the named targets and is not a whole-repository CI rebuild).

This note documents the established operator-algebraic Peirce defect spine and
its kernel-checked bridges to matrix exterior-algebra Yang–Mills connection
curvature (`SelfDualConnectionCurvatureYangMillsBridge`), the finite-stage
two-sheet Hestenes–Krein stage system and its filtered colimit
(`TwoSheetKreinStageSystem`), the `Cl(1,1)^{\otimes n}` inductive colimit
`Limit` (`PeirceTetraktysColimitCoercivity`), infinite-dimensional Cantor
boundary Hilbert sewing anomaly cancellation (`ConcreteHilbertSewnAnomaly`),
noncommutative Weyl–Cartan and Iwasawa KAN / polar equivariance
(`NoncommutativeWeylCartanKANPolarEquivariance`, `WeylTraceKANPolarEquivariance`),
off-diagonal Bloch-ball Umegaki relative entropy / quantum Spohn dissipation
(`BlochBallUmegakiAndQuantumSpohn`, `SchrodingerGKSLFlowBridge`), and the Euclidean
lattice Osterwalder–Schrader transfer semigroup & mass gap
(`OsterwalderSchraderTransferSemigroupAndMassGap`), while strictly
separating these proved algebraic, lattice, dissipative, and trace-extension theorems from
unproved continuum 4D quantum Yang–Mills PDE/Wightman mass-gap claims in the $a \to 0$ limit or
multipartite entanglement claims.

## Established operator-algebra layer

The reusable polynomial is owned by
`InfoGeometry.Core.IdempotentGraphGrassmannian`: for an element `x` of a
unital associative ring, `idempotencyDefect x := x * x - x`. The Peirce spine
defines the two corner projections, their even and odd parts, the boundary
generators, and the quadratic cycles. The
`InfoGeometry.OperatorAlgebra.PeirceDefectBridge` imports those owners and
proves, for an idempotent `P` and arbitrary `X` in an associative ring,

```text
evenGrade P (idempotencyDefect X)
  - idempotencyDefect (evenGrade P X) = genV P X X
```

It also proves `oddGrade P X * oddGrade P X = genV P X X`, the separate
`qgtPlus` and `qgtMinus` corner identities, and that `genV = 0` exactly when
both corner cycles vanish. If `X * X = X`, then
`idempotencyDefect (evenGrade P X) = -genV P X X`. These are ring identities;
the source explicitly does not identify `genV` with analytic flux, positivity,
or tensor separability.

There is a concrete noncommutative witness in
`PeirceDefectMatrixWitness`: the carrier is the full matrix ring
`Matrix (Fin 2) (Fin 2) ℚ`; the cut is idempotent; the symmetric rank-one
matrix state is self-adjoint and idempotent; and the state does not commute
with the cut. The source proves `genV = (1/4) • 1` and that the pinched
idempotency defect is `-(1/4) • 1`, hence nonzero. It also supplies a
noncommuting mixed-operator counterexample to a proposed commutator replacement
and verifies the corrected ordered anticommutator formula.

`PeirceSpine.TwoStateSandwich` proves further ordered
two-chart products, including `(P - N₊) V (P + N₋) = Q₊ - Q₊²` and
`(P - N₊) Σ (P + N₋) = Q₊ + Q₊²`. The checked-in archetype ledger records why
the alternative submitted signs/formulas fail. `PeirceSpine.DefectTower` is an existing owner for orthogonal defect iteration,
support, and corner projection statements. The staged change in `Unipotent.lean`
adds a natural-number unipotent idempotent tower, proves each finite stage
idempotent, and derives parent/child relations. The Peirce bridge composes this
tower with the pinching-defect theorem and the two-state conjugation invariant.
In addition, `PeirceDefectBridge` defines the inner Peirce grading derivation
`peirceGradingDeriv P X := comm P X`, the non-Abelian covariant derivative
`peirceCovariantDeriv P A C X := peirceGradingDeriv P X + comm (genPhi P A C) X`,
and the Maurer–Cartan curvature
`peirceMaurerCartanCurvature P A C := peirceGradingDeriv P (genPhi P A C) + genPhi P A C * genPhi P A C`,
and proves `peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills`
(Leibniz rule, decomposition `peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`
into anti-self-dual odd and self-dual even components under `parityConj P`, and
the covariant Bianchi / self-dual Yang–Mills identity
`peirceCovariantDeriv P A C (genV P A C) = 0`).

## Established two-sheet Krein, Yang–Mills, and colimit bridges

1. **Two-Sheet Krein Stage System & Filtered Colimit Bridge (`InfoGeometry.Categorical.TwoSheetKreinStageSystem`)**:
   Imports `InfoGeometry.OperatorAlgebra.PeirceDefectBridge` and proves
   `twoSheetKrein_peirce_spine_and_colimit_bridge`: on `SheetMatrix`, `fPlus` is
   a Peirce idempotent with `1 - fPlus = fMinus`, `kreinAction` swaps `peirce11`
   with `peirce00` and `qgtPlus` with `qgtMinus` while preserving `genV`, and in
   the filtered colimit `Module.End ℝ (Carrier StageFunctor)` the induced
   operator `P_colim = twoSheetColimitEnd plusStage` is an idempotent satisfying
   both the Peirce pinching–defect identity and
   `peirceCovariantDeriv P_colim A_colim C_colim (genV P_colim A_colim C_colim) = 0`.
   *Scope boundary*: `StageFunctor` in `TwoSheetKreinStageSystem` is the constant
   diagram `(Functor.const ℕ).obj (ModuleCat.of ℝ SheetMatrix)`.

2. **Matrix Exterior-Algebra Yang–Mills Connection Curvature Bridge (`InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge`)**:
   Imports `InfoGeometry.OperatorAlgebra.PeirceDefectBridge` and proves
   `peirce_defect_connection_curvature_and_yang_mills_bridge` on
   `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)`: for an idempotent matrix `P`
   and chiral connection `A_conn = genPhi P A_op C_op`, whenever
   `matrixExteriorDerivative d A_conn = peirceGradingDeriv P A_conn`,
   `curvatureFromConnection d A_conn = genJ P A_op C_op + genV P A_op C_op` with
   even Peirce grade `genV P A_op C_op`; for `d = 0`,
   `curvatureFromConnection 0 A_conn = genV P A_op C_op`,
   `covariantDerivative A_conn 0 (genV P A_op C_op) = 0`, and self-duality
   implies `covariantDerivative A_conn 0 (matrixHodgeStar star (curvatureFromConnection 0 A_conn)) = 0`.
   *Scope boundary*: This is an algebraic matrix-form theorem; it does not claim
   analytic PDE existence on a smooth 4-manifold.

3. **`Cl(1,1)^{\otimes n}` Inductive Colimit Coercivity, Tensor-Tower Krein Polarization, Log-CFT Monodromy, `FibonacciK0`, & `Cl(5,5)` Bott-Boundary Spinor Bridge (`InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity`)**:
   Proves `limit_peirceBdGHamiltonian_noncomm_sq_and_trace_positivity`,
   `limit_pentagon_hexagon_heptagon_braiding_and_klein_penrose`,
   `limit_polygon_lucas_trace_coercivity_hierarchy` (establishing the Hermitian-square
   factorizations of `V`, `V²`, `V³` and the monotone trace coercivity chain
   `0 ≤ tau (star X * X) ≤ tau (star X * X) + 5 * tau (star X * V * X) ≤ tau (star X * L₅ * X) ≤ tau (star X * L₆ * X) ≤ tau (star X * L₇ * X)`),
   `stageKreinPairing_bondMap_and_limit_descent` & `limit_krein_polarization_and_self_dual_yang_mills`
   (upgrading the constant-diagram `TwoSheetKreinStageSystem` theorem to the nontrivial
   `2ⁿ × 2ⁿ` tensor-tower colimit `Limit`, proving multi-step `bondMap` invariance of
   `stageKreinPairing`, positive/negative-definite sheet polarization of `limitKreinPairing`,
   and the colimit Maurer–Cartan self-dual Yang–Mills / Bianchi identity
   `peirceCovariantDeriv P A C (genV P A C) = 0`),
   `limit_logCft_jordan_monodromy_and_fibonacciK0_penrose_bridge` (transporting the
   operator-ring Virasoro Jordan cell `opVirasoroL0Cell`, logarithmic monodromy
   `opLogMonodromy`, and `FibonacciGrothendieckRing` representation `fibK0ToPeirceOp`
   into `Limit`),
   `limit_tetraktys_clifford_exterior_and_cayley_dickson_boost_bridge` and
   `limit_kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge`
   (transporting the Clifford–Exterior–Interior Tetraktys calculus, Cayley–Dickson
   paracomplex boost `splitComplexToBoostOp` vs. elliptic hypercomplex `hypercomplexToRotOp`
   doubling, Kantor triple product `opKantorTriple`, 5-graded anomaly generators
   `bdgUpperAnomaly` and `bdgLowerAnomaly`, and zero-shell operator cyclotomic
   characteristic polynomials `opCharPolyPhi6`, `opCharPolyPhi3`, `opCharPolyTransfer`
   into `Limit`),
   and `cl55_bott_spinor_stage5_peirce_bdg_and_klein_penrose_bridge` (embedding
   `Cl(5,5)` faithfully into `Stage 5` via `cl55ToStage5` and transporting the
   vacuum spinor idempotent, `peirceBdGHamiltonian`, and Stage `D₂₅` Pentagon–Hexagon–Heptagon
   and Klein-bottle Penrose operators into `Limit`).

4. **All-`m` Polygon Lucas–Fibonacci & Eisenstein–Chebyshev Braiding, Covariant Bianchi Tower, Colimit Coercivity, & Multi-Period `Cl(5,5)` Bott Spinor Synthesis (`InfoGeometry.Canonical.PeircePolygonKreinBottMasterSynthesis`)**:
   Proves `all_m_penrose_kite_dart_power_inflation_and_lucas_recurrence` (extending the
   Pentagon/Hexagon/Heptagon Lucas and Fibonacci operators to arbitrary `m : ℕ`, proving
   `(penroseKiteOp P A C) ^ (m + 1) = polygonFibSeq P A C (m + 1) * penroseKiteOp P A C + penroseDartOp P A C * polygonFibSeq P A C m`
   and the all-`m` Klein-bottle meridian intertwining identity),
   `peirceCovariantDeriv_polygon_tower_and_cross_carrier_yang_mills` (proving covariant
   constancy of `polygonFibSeq` and `polygonLucasGen` for all `m : ℕ` across `[Ring B]`,
   the two-sheet Krein filtered colimit `Module.End ℝ (Carrier StageFunctor)`, and
   `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)`),
   `limit_all_m_polygon_fibonacci_and_lucas_trace_coercivity_tower` (proving non-negativity
   and monotone trace coercivity of `polygonFibSeq` and `polygonLucasGen` for all `m : ℕ`
   in `Limit`), `cl55_multi_period_bott_spinor_tower_and_all_m_colimit_bridge`
   (extending `cl55ToStage5` across all `8k` Bott periods `Stage (5 + 8 * k)` via
   `cl55ToBottStage k` with exact colimit invariance in `Limit`),
   `tetraktys_witt_clifford_fourfold_ladder_and_polygon_bivector_bridge` (unifying the Witt
   lightcone interior/exterior and `Cl(1,1)` 1-vector viewpoints of the 4-fold Tetraktys
   `(Φ, J, V, Σ)` with the bivector action on `polygonFibSeq`),
   `peirceKleinHom_eq_group_sandwich_character_channels_and_fourier_projectors` (identifying
   all four elements of the unit-square Klein four-group action `peirceKleinHom hP A C hV`
   with the sandwich character channels `grpId, grpPhi, grpSig, grpJ` and their Fourier
   projectors `fourierV..fourierSig`),
   `all_m_eisenstein_power_linearization_radical_factorization_and_bianchi` (proving the
   elliptic `γ = -1` partner power linearization `(peirceTransferJ P A C) ^ (m + 1) = eisensteinSeq P A C (m + 1) * peirceTransferJ P A C - genV P A C * eisensteinSeq P A C m`,
   radical factorization `W^m - W̄^m = eisensteinSeq P A C m * radicalLetterMinus P A C`,
   and covariant Bianchi constancy of `eisensteinSeq` and `eisensteinLucasGen`), and
   `cl55_multi_period_bott_tetraktys_kantor_cyclotomic_and_eisenstein_colimit_bridge`
   (intertwining the all-`m` Eisenstein sequence, Cayley–Dickson paracomplex boost norm,
   Kantor triple product, 5-graded anomalies, and operator cyclotomic characteristic
   polynomials across all `8k` Bott periods into `Limit`),
   `dressed_kirillov_reshetikhin_t_system_and_symbol_alphabet_master_bridge` (proving the
   all-`m` Kirillov–Reshetikhin `T`-system Cassini–Hirota exchange identities for
   `polygonFibSeq` and `eisensteinSeq` and their invariance under horizon-preserving
   dressings `dressedCurv U U_inv`),
   `limit_stage_D27_quantum_affine_dual_canonical_and_partial_flag_bridge` (transporting
   Stage `D₂₇` Drinfeld new presentation loop currents, Kirillov–Reshetikhin transfer
   operators, four-mass-box square-root symbol letters, and nested partial flag variety
   embeddings into `Limit`),
   `limit_stage_D28_uhf_heisenberg_sugawara_virasoro_bridge` (transporting Stage `D₂₈`
   chiral parity charges, affine Heisenberg current modes, Sugawara quadratic
   stress-energy tensors, Virasoro central defect additivity, and UHF inductive tower
   identities into `Limit`),
   `cl55_multi_period_bott_and_limit_stages_D29_D30_D31_master_bridge` (transporting
   Stage `D₂₉` all-`(r,s)` Heisenberg–Virasoro Witt derivations, Stage `D₃₀` length-3
   partial flag parabolic radicals, and Stage `D₃₁` all-scale `k`, all-depth `d`
   UHF–unipotent tower / two-state chart sandwiches across `cl55ToBottStage p` into `Limit`),
   `dressed_drinfeld_loop_currents_and_all_m_symbol_rationalization` (proving the exact
   unipotent horizon-dressing transformation of Drinfeld loop currents and all-`(m, l)`
   rationalization of `algSymbolFactorPlus`/`algSymbolFactorMinus` evaluated at
   `polygonFibSeq P A C m` and `eisensteinSeq P A C l`),
   `partial_flag_three_idempotent_partition_and_borel_dressing_bridge` (proving the
   3-idempotent partition of unity `(P₁, flagStratumIdem P₁ P₂, 1 - P₂)` and converse
   reconstruction from any orthogonal 3-idempotent partition `E₁ + E₂ + E₃ = 1`, the
   Borel nilpotent radical Steinberg commutator `[borelCorner12, borelCorner23] = borelCorner13`,
   and the exact unipotent Maurer–Cartan dressing cocycles for all three Borel corners),
   and `cl55_multi_period_bott_stage_D26_D27_dressing_and_quantum_affine_colimit_bridge`
   (transporting Stages `D₂₆`–`D₂₇` and the dressed Drinfeld / Borel partial-flag bridges
   across all `8k` Bott periods `ofStage (5 + 8 * k) ∘ cl55ToBottStage k : Cl55 →+* Limit`),
   and `limit_stage_D29_zorn_matrix_algebra_and_complex_tetrad_bridge` (transporting the
   Stage `D₂₉` Oliveira–Maia split Cayley / Zorn–Peirce matrix representation `zornMatrix`,
   exact non-commutative Zorn block product, Zorn quadratic norm `zornNorm`, complex tetrad
   symmetric metric `zornTetradSym` vs. antisymmetric 2-form `zornTetradSkew`, and mixed
   tetrad squares into `Limit`, together with `zornMatrix_self_eq_and_chiralPlane_soldering`
   soldering `zornMatrix` to `zornChiralPlaneMatrix`), and
   `cl55_multi_period_bott_and_limit_stage_D29_D32_zorn_tetrad_drinfeld_master_bridge`
   (proving the Stage `D₃₂` upper-sheet identity
   `((genPhi P A₁ C₁ + genJ P A₂ C₂)^2) * P = ((genV P A₁ C₁ - genV P A₂ C₂) - zornTetradSkew P A₁ C₁ A₂ C₂) * P`,
   the full-ring lower-sheet QGT residual `-2 • (qgtMinus P A₁ C₂ - qgtMinus P A₂ C₁)`,
   the mode-graded Zorn–Drinfeld–Virasoro matrix `zornDrinfeldMatrix r r P A C` and its
   Zorn norm `opPow (r + r) (genV P A C) - virasoroModeEven (r + r) P A C`, and
   horizon-preserving dressing invariance `dressedCurv_zornMatrix_and_zornNorm_invariance`,
   and transporting them across `cl55ToBottStage p` into `Limit`), and
   `limit_stage_D30_furey_lie_jordan_corner_hopf_bridge` (transporting
   Stage `D₃₀` (`N₁ → N₅`) Furey's universal Lie–Jordan product `fureyProduct`,
   its Tetraktys evaluation `fureyProduct_genPhi_genJ_tetraktys`, quaternionic
   sector symmetry breaking `chargeQ6 - chargeY6 = 3 • quatChiralInv`, the
   multiplicative corner map `inducedEndoRep` on an associative ring, and the non-commutative operator
   Hopf coordinate identities `hopfCoordZ`, `hopfCoordPerp`, `hopfRadiusSq` into `Limit`).
   Further extended in
   `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TelegrapherTwoStateMasterPoset.lean`
   and `lean/InfoGeometry/Canonical/PeirceTelegrapherVirasoroColimitBridge.lean`:
   - `MasterSpineStage` (`A₁ → A₈₂` unified 82-stage master causal poset extending
     `NonCommutativeSpineStage` via `ofSpine58_strictMono`),
   - Tier 1 (`A₇₀ → A₇₆`): defect-scaled cone nilpotency & cubic relations, unipotent
     double-pass & parity round-trip, dual Steinberg braid & Bruhat parity, parity
     double-derivation intertwining & vorticity factorization, second-order telegrapher
     operator `curvatureDoubleCommutator`, even/odd defect telegrapher relations, 4th-order
     master metriplectic polynomial `metriplecticMasterPoly4Op`, and all-mode single-sheet
     Drinfeld–Virasoro–MOG decoders `mog24SheetPlus` / `mog24SheetMinus` on
     `drinfeldPhiPlus r` and `drinfeldPhiMinus r`,
   - Tier 2 (`A₇₇ → A₈₂`): homogenized channel kernels & unit-defect exclusions, graded
     defect perturbation & parity products, Wilson plaquettes & logarithmic corner pullbacks,
     all-depth two-state local chart sandwiches, star-grading anti-involution & ideal chart
     pairings, and block-lower `tcrDecoderFullOp` closure,
   - Tier 3 (`two_sheet_krein_and_yang_mills_telegrapher_virasoro_sheet_bridge`,
     `limit_stages_A51_to_A82_kantor_telegrapher_virasoro_sheet_and_two_state_colimit_bridge`,
     `cl55_multi_period_bott_stages_A51_to_A82_master_colimit_bridge`): instantiating `A₅₁–A₈₂`
     across `Module.End ℝ (Carrier StageFunctor)`, `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V_ext)`,
     `Limit`, and `Stage (5 + 8 * p)` (`cl55ToBottStage p`).

5. **Bipartite Separability vs. Peirce Casimir Defect (`InfoGeometry.OperatorAlgebra.PeirceBiSandwich.BipartiteSeparabilityAndPeirceEntanglement`)**:
   Closes lines 232–234 by explicitly determining the relation between reduced state purity/idempotency defect and single-cut Peirce Casimir defect $\mathrm{genV}$. On unit two-rebit pure state vectors $\psi : \mathrm{Fin}\ 2 \times \mathrm{Fin}\ 2 \to \mathbb{R}$ (`IsUnitState ψ`) with amplitude matrix $C_\psi = \mathrm{amplMat}\ \psi$, density projector $\Pi_\psi = \mathrm{pureProj}\ \psi$, and subsystem-$B$ partial trace $\mathrm{Tr}_B$:
   - Proves $\mathrm{Tr}_B(\Pi_\psi) = C_\psi C_\psi^T$ (`partialTraceB_pureProj`) and $\mathrm{Tr}(\mathrm{Tr}_B(\Pi_\psi)) = 1$ (`trace_partialTraceB_pureProj`).
   - Via $2 \times 2$ Cayley–Hamilton / trace-determinant reduction, proves the exact identity $\delta(\mathrm{Tr}_B(\Pi_\psi)) = -(C_\psi.\det^2) \bullet 1$ (`idempotencyDefect_partialTraceB_pureProj`).
   - Establishes the exact three-way equivalence `IsProductState ψ ↔ (amplMat ψ).det = 0 ↔ delta (partialTraceB (pureProj ψ)) = 0` (`isProductState_iff_idempotencyDefect_zero`).
   - Decisively separates bipartite tensor entanglement from single-cut Peirce defect `genV` (`peirce_defect_differs_from_entanglement`):
     * Separable product superposition `productSuperpos` ($|+\rangle \otimes |0\rangle$): `IsProductState` holds and $\delta(\mathrm{Tr}_B) = 0$, yet for local single-cut $P_{\mathrm{loc}}$ it has $\mathrm{genV}\ P_{\mathrm{loc}} \ne 0$.
     * Maximally entangled Bell state `bellPhiPlus` ($(|00\rangle + |11\rangle)/\sqrt{2}$): `¬ IsProductState` and $\delta(\mathrm{Tr}_B) = -(1/4) \bullet 1 \ne 0$, and $\mathrm{genV}\ P_{\mathrm{loc}} \ne 0$.
   *Scope boundary*: Demonstrates that non-vanishing $\mathrm{genV}$ signifies failure of Peirce projectability for the individual cut operator, not bipartite entanglement of the underlying state vector.

6. **Custodial Twin Involution, All-Loop Protection & Josephson Condensate (`InfoGeometry.OperatorAlgebra.PeirceBiSandwich.CustodialTwinLoopAndJosephsonLattice`)**:
   Proves the finite-matrix custodial twin symmetry preventing radiative odd-power leakage:
   - In $M_8(\mathbb{R})$, proves the $\mathbb{Z}_2$ real freeze (`z2_real_freeze_M8`): $D_{1,8}$ is symmetric ($D_{1,8}^T = D_{1,8}$) and $D_{2,8}$ is skew-symmetric ($D_{2,8}^T = -D_{2,8}$), while $\Sigma$ is symmetric and cannot generate unitary phase rotations.
   - In $\mathrm{Mat16Prod} = M_8(\mathbb{R}) \otimes M_2(\mathbb{R})_{\mathrm{phase}}$, adjoining $J_{\mathrm{phase2}}$ yields the skew-adjoint charge generator $G_{U(1),16} = \Sigma \otimes J_{\mathrm{phase2}}$, generating the $U(1)$ BdG circle $\Delta_{U(1)}(\theta)$ with gap $\Delta_{U(1)}(\theta)^2 = V_{16}$ (`comm_G_U1_D1`, `delta_U1_sq`).
   - Proves custodial twin involution $W_{\mathrm{twin}} = \Phi + P_0$ (`custodial_twin_involution_Z`): $W_{\mathrm{twin}}^2 = 1$, $W_{\mathrm{twin}}^T = W_{\mathrm{twin}}$, commutes with the horizon $[W_{\mathrm{twin}}, H_{\mathrm{hor}}] = 0$, fixes $P_0$, and odd-parity conjugates $D_{1,8}$ ($W_{\mathrm{twin}} D_{1,8} W_{\mathrm{twin}} = -D_{1,8}$).
   - Proves all-loop polynomial odd-power vanishing on $P_0$: $P_0 F(H_{\mathrm{hor}}) D_{1,8}^{2m+1} G(H_{\mathrm{hor}}) P_0 = 0$ for all $F, G \in \mathbb{R}[X]$ (`custodial_all_loop_odd_power_vanishing`), and boost commutation for even powers $[K_8, D_1^{2m}] = 0$ (`custodial_boost_comm_even_powers`).
   - Proves 1-loop parity-odd birefringence: $P_0 H \Delta_{U(1)}(\theta) H P_0 = (2 \sin \theta) \bullet M_{\mathrm{biref}}$ (`one_loop_parity_odd_birefringence`).
   - Proves Josephson cosine coupling $( \Delta_{U(1)}(\theta_x) \Delta_{U(1)}(\theta_y) )_{\mathrm{trace}} = 8 \cos(\theta_x - \theta_y)$ (`josephson_cosine_coupling`) and sub-isometric defect $\delta(V_{16,\varepsilon}) = (-\varepsilon(1-\varepsilon)) \bullet V_{16}$ (`casimirDefect_V16_eps`).
   *Scope boundary*: Loop vanishing is established algebraically via polynomial functional calculus (`Polynomial.aeval`) on $M_8(\mathbb{R})$; it is not a continuum path-integral Feynman diagram evaluation.

7. **Lattice Gauge Invariance, Elitzur Projection & N-Link Chain (`InfoGeometry.OperatorAlgebra.ElitzurLatticeGaugeProjection`, `InfoGeometry.OperatorAlgebra.NLinkElitzurChainAndCompactU1Gauge`)**:
   Formalizes local gauge invariance and physical state projection on finite and 1D lattice chains:
   - Classical finite Haar–Reynolds Gibbs gauge invariance (`haarReynolds_gibbs_invariance`): local character-covariant observables vanish identically in expectation (`elitzur_local_gauge_expectation_zero`: $\langle O \rangle = 0$) for all temperatures and couplings, and in thermodynamic limits (`elitzur_thermodynamic_limit_zero`).
   - $\mathbb{Z}_2$ link-Higgs model (`z2_link_higgs_elitzur_vs_wilson_string`): bare expectation vanishes $\langle \sigma_0 \rangle = 0$, while Wilson-dressed string is strictly positive $\langle \sigma_0 U_{01} \sigma_1 \rangle = \tanh J > 0$ for $J > 0$.
   - Quantum representation-theoretic physical projection $P_{\mathrm{phys}} = \rho.\mathrm{averageMap}$: annihilates character-covariant operators $P_{\mathrm{phys}} \circ A \circ P_{\mathrm{phys}} = 0$ (`P_phys_comp_A_comp_P_phys_eq_zero`).
   - $N$-link chain with local vertex gauge group $(\mathrm{Fin}(N+1) \to \mathbb{Z}^\times)$: exact local matter vanishing $\langle \sigma_x \rangle = 0$ (`expectChain_sigma_zero`), two-point vanishing $\langle \sigma_x \sigma_y \rangle = 0$ for $x \ne y$ (`expectChain_sigma_pair_zero`), closed-form Wilson string expectation $\langle W_{0,L} \rangle = (\tanh J)^L$ (`expectChain_wilson_eq_tanh_pow`), and exponential perimeter/mass-gap decay $(\tanh J)^L \to 0$ (`expectChain_wilson_tendsto_zero`).
   - Compact $U(1)$ continuous Haar integral: normalized translation-invariant average proves exact charge-$q$ Elitzur vanishing for all $q \ne 0$ (`u1HaarAvg_charge_vanishing`).
   - Euclidean transfer semigroup & Osterwalder–Schrader reflection positivity (`InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap`): constructs $T(J) \in M_2(\mathbb{R})$ (`transferMat`, `transferMat_posDef`), spectral projector decomposition $\widetilde{T}(J)^L = P_0 + (\tanh J)^L P_1$ (`normTransferMat_pow`), strictly positive spectral mass gap $\Delta(J) = -\log(\tanh J) > 0$ (`spectralMassGap_pos`), exponential clustering $(\tanh J)^L = e^{-L\Delta(J)} \to 0$ (`normTransferMat_pow_eq_exp_gap`, `normTransferMat_clustering_tendsto_zero`), exact bridge to the Elitzur Wilson string expectation (`expect_wilson_from_transferMat`), non-commutativity witness `transferMat_noncomm_witness`, and transfer-matrix-weighted 2-slice Osterwalder–Schrader reflection positivity (non-trivial time-reflection involution `osReflect`, Boltzmann partition expectation `osExpectation`, `os_reflection_positivity` for $J > 0$, antiferromagnetic $J < 0$ failure `os_reflection_positivity_fails_antiferro`, Cauchy–Schwarz `os_cauchy_schwarz`, and $L$-step semigroup positivity `os_semigroup_reflection_positivity`).
   *Scope boundary*: Discrete lattice gauge theory, 1D compact chain models, and discrete transfer-matrix semigroups; does not establish 4D continuum Wightman/Osterwalder–Schrader gauge quantum field theory in the $a \to 0$ limit.

8. **Solve et Coagula Non-Commutative Peirce–Aporia Poset (`InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset`)**:
   Formalizes the 5-stage causal compilation chain $\mathcal{E}\mathcal{C}_1 \prec \dots \prec \mathcal{E}\mathcal{C}_5$ uniting the Peirce defect spine, aporia iterations, and Clifford towers:
   - $\mathcal{E}\mathcal{C}_1$ (`EC1_BinaryCut`): Primordial binary cut idempotent complementation ($Q^2 = Q$, $S^2 = 1$) and characteristic-free derivation/commutator laws ($P X = X P \leftrightarrow \mathrm{oddGrade}\ P\ X = 0$) (`binary_cut_idempotent_and_grading_laws`, `binary_cut_commute_iff_corners_zero`).
   - $\mathcal{E}\mathcal{C}_2$ (`EC2_PeirceAnatomy`): Fourfold relational Peirce decomposition $X = X_{11} + X_{10} + X_{01} + X_{00}$ with uniqueness and non-commutative quiver multiplication table (`peirce_fourfold_decomp`, `peirce_fourfold_direct_sum_unique`, `peirce_fourfold_mul_table`), plus order-asymmetry witness (`peirce_order_asymmetry_witness`).
   - $\mathcal{E}\mathcal{C}_3$ (`EC3_TranscendentQuartet`): Transcendent quartet algebra $(\Phi, J, V, \Sigma)$ with universal creation lock ($\mathrm{genV} = 0 \leftrightarrow \mathrm{genSig} = 0 \leftrightarrow \mathrm{qgtPlus} = 0 \wedge \mathrm{qgtMinus} = 0$) (`transcendent_quartet_algebra`, `transcendent_creation_lock_iff`), Bruhat unipotent tilt and Maurer–Cartan Bianchi identity $\nabla_A V = 0$ (`bruhat_tilt_and_maurer_cartan_bianchi`), and non-commutative fiber trace (`noncomm_fiber_trace_genSig_and_supertrace`).
   - $\mathcal{E}\mathcal{C}_4$ (`EC4_AporiaDefectTower`): Socratic aporia boundary defect $\delta(P + \Phi) = V$ (`socratic_aporia_bridge_and_pinching`), meta-cognitive defect iteration $\delta^{n+1}(P + \Phi) = \delta^n(V)$ and Newton–Peirce tower (`meta_cognitive_defect_and_newton_tower`), infinite non-periodic aporia orbit in $M_2(M_2(\mathbb{Z}))$ (`infinite_nonperiodic_aporia_orbit_nestedMatZ`), and transport across $Cl$-tower morphisms and colimits (`clTower_and_colimit_aporia_transport`).
   - $\mathcal{E}\mathcal{C}_5$ (`EC5_MasterCoagulation`): Bounded acyclic causal poset `SolveEtCoagulaNode`, covering relation `Covers`, strict rank monotonicity `ecRank_strictMono`, irreflexivity/acyclicity (`covers_irreflexive`, `covers_acyclic`), and `master_solve_et_coagula_noncommutative_synthesis`.
   *Scope boundary*: The poset structures the algebraic transformation pipeline from binary cut to colimit transport; it is not a spacetime causal causal-set model.

9. **Infinite-Dimensional Hilbert-Space Sewn Boundary Anomaly Cancellation on $H_{\ell_2}$ (`InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly`)**:
   Lifts the two-sheet modular swap involution $J$ and chiral fundamental symmetry $\varepsilon$ from the fiber $\mathrm{DoubledSpace}\ E = \mathrm{WithLp}\ 2\ (E \times E)$ onto the completed binary Cantor boundary Hilbert space $H_{\ell_2}(E) := \ell_2(\mathrm{BinaryCantorBoundary} \to \mathrm{DoubledSpace}\ E)$ with native inner product `lp.instInnerProductSpace`:
   - Proves isometric involution: $J_{\ell_2}^2 = 1$ (`J_lp_clm_comp_self`, `J_lp_clm_isometry`) and $\varepsilon_{\ell_2}^2 = 1$ (`epsilon_lp_clm_comp_self`, `epsilon_lp_clm_isometry`).
   - Proves $\mathrm{Cl}(1,1)$ anticommutation: $J_{\ell_2} \circ \varepsilon_{\ell_2} = -(\varepsilon_{\ell_2} \circ J_{\ell_2}) = K_{\ell_2}$ (`J_lp_clm_anticomm_epsilon_lp_clm`, `J_lp_clm_comp_epsilon_lp_clm`).
   - Proves self-adjointness of $J_{\ell_2}$ with respect to the $\ell_2$ inner product: $\langle J_{\ell_2} \psi, \varphi \rangle = \langle \psi, J_{\ell_2} \varphi \rangle$ (`inner_J_lp_clm_selfAdjoint`).
   - Intertwines with non-commuting Cuntz $O_2$ branch isometries ($S_{\mathrm{left}} \circ S_{\mathrm{right}} \ne S_{\mathrm{right}} \circ S_{\mathrm{left}}$): proves exact sewing invariance $J_{\ell_2} \circ S_i \circ J_{\ell_2} = S_i$ (`S_left_lp_clm_sewn_invariant`, `S_right_lp_clm_sewn_invariant`) and commutation with $\varepsilon_{\ell_2}$.
   - Proves canonical non-zero $J_{\ell_2}$-fixed Cantor boundary vacuum state $\psi_{\mathrm{sewn}} = (\delta_{+++...}) \otimes (1, 1)$ (`canonicalCantorSewnState_ne_zero`, `canonicalCantorSewnState_fixed`).
   - **Infinite-Dimensional Anomaly Cancellation Theorems**:
     * For every $J_{\ell_2}$-sewn bounded operator $B$ ($J_{\ell_2} \circ B \circ J_{\ell_2} = B$), the swap-paired chiral expectation cancels identically: $\langle v, \varepsilon_{\ell_2}(B v) \rangle + \langle J_{\ell_2} v, \varepsilon_{\ell_2}(B(J_{\ell_2} v)) \rangle = 0$ (`infinite_hilbert_paired_chiral_summand_zero`).
     * For any $J_{\ell_2}$-fixed state $\psi$ ($J_{\ell_2} \psi = \psi$), the chiral expectation vanishes identically: $\langle \psi, \varepsilon_{\ell_2}(B \psi) \rangle = 0$ (`infinite_hilbert_sewn_chiral_expectation_zero`).
     * For any $J_{\ell_2}$-paired family $(e_i)_{i \in \iota}$ with summable diagonal entries, the infinite-series chiral index vanishes: $\sum'_{i \in \iota} \langle e_i, \varepsilon_{\ell_2}(B e_i) \rangle = 0$ (`infinite_hilbert_tsum_chiral_index_zero`).
     * Concrete non-zero Cantor boundary state anomaly vanishing: $\langle \psi_{\mathrm{sewn}}, \varepsilon_{\ell_2}(B \psi_{\mathrm{sewn}}) \rangle = 0$ (`canonicalCantorSewnState_chiral_zero`).
   *Scope boundary*: Closes the boundary anomaly and Krein deficit on the infinite-dimensional $\ell_2$ completed Cantor boundary Hilbert space; does not construct continuum 4D Lorentzian quantum field theory anomaly polynomials on curved spacetimes.

10. **Noncommutative Weyl–Cartan Decomposition, Iwasawa $K A N$ & Polar Equivariance (`InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance`, `InfoGeometry.Canonical.WeylTraceKANPolarEquivariance`)**:
    Establishes the acyclic theorem-dependency poset $(\mathcal{K}\mathcal{P}, \preceq)$ (`kpPoset_actual_dependencies`) governing the two-sheet Cartan/trace split, the Iwasawa $K A N$ subgroups, and unitary/symmetry equivariance across arbitrary rings `[Ring B]` and $\star$-rings `[Ring B] [StarRing B]`:
    - $\mathcal{K}\mathcal{P}_1$: Proves the exact 3-component Cartan split $2 \bullet M = M_{\mathrm{Weyl}}(M) + M_{\mathrm{sym}}^0(M) + M_{\mathrm{antisym}}^0(M)$ (`weyl_cartan_split_and_noncommutative_trace_to_det`, `noncommutative_weyl_cartan_trace_determinant`), trace vanishing, transposition symmetries, and the noncommutative Plemelj–Newton trace-to-symmetrized-determinant identity $(\mathrm{Tr} M)^2 - \mathrm{Tr}(M^2) = \mathrm{symDet} M$.
    - Characterizes centrality of diagonal embeddings (`fiberEmbed_central_iff`) with explicit non-central witness over $B = M_2(\mathbb{Z})$ (`weylScalePart_noncentral_witness`), and verifies $\mathfrak{gl}_2$ Lie brackets $[\gamma_1, \sigma] = -2\omega$, $[\omega, \gamma_1] = 2\sigma$, $[\omega, \sigma] = -2\gamma_1$.
    - $\mathcal{K}\mathcal{P}_2$: Proves Iwasawa $K, A, N$ subgroup multiplication laws and the Polar Gram reduction eliminating unitary $K$: $M^\dagger M = (A N)^\dagger (A N)$ under $K^\dagger K = 1$, with noncommutative Schur complement recovery $(M^\dagger M)_{11} - n^\star (M^\dagger M)_{00} n = a_-^\star a_-$ (`iwasawa_kan_subgroups_and_polar_gram_reduction`, `kan_gram_formula`, `kan_gram_schur_complement`).
    - $\mathcal{K}\mathcal{P}_3$: Proves unitary symmetry equivariance of polar decompositions over any $\star$-ring: $G M G^{-1} = (G U G^{-1})(G P G^{-1})$ (`polar_decomposition_unitary_equivariance`, `polar_matrix_unitary_equivariance`).
    - $\mathcal{K}\mathcal{P}_4$: Proves 4-way $K A N$ conjugation equivariance under diagonal Borelian $A(g_+, g_-)$, non-Abelian fiber gauge $\iota(g)$, chirality parity $\gamma_1$, and Weyl reflection $\sigma$ (`iwasawa_kan_symmetry_equivariance`).
    - $\mathcal{K}\mathcal{P}_5$: On $GL^+(2, \mathbb{R})$, proves global existence and uniqueness of Iwasawa $K A N$ factorization (`real_gl2_pos_iwasawa_factorization`, `real_gl2_pos_kan_unique`), frame-push relative Iwasawa factorization (`relative_iwasawa_factorization`, `relative_iwasawa_unique`), and polar decomposition (`real_gl2_pos_polar_factorization`, `real_gl2_pos_polar_unique`, `real_gl2_pos_metric_polar_unique`) with positive-definite symmetric factor $P$, metric polar uniqueness, and orthogonal conjugation equivariance.
    *Scope boundary*: Finite-matrix and operator-ring algebraic identities; does not imply infinite-dimensional diffeomorphism or non-compact gauge group path-integral convergence.

11. **Welded 3D Non-Commutative GKSL Semigroup, Bloch-Ball Umegaki Geometry & Quantum Spohn Synthesis (`InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn`, `InfoGeometry.Modular.SchrodingerGKSLFlowBridge`)**:
    Closes the off-diagonal coherence gap for open-system two-sheet dynamics on full self-adjoint unit-trace states $\rho \in M_2(\mathbb{C})$ inside the open Bloch ball $\|\vec{r}(\rho)\|^2 = z^2 + 4|\rho_{01}|^2 < 1$:
    - Evaluates continuous functional calculus `CFC.log ρ` and `CFC.log (gibbsDensityC θ)` via exact two-sheet spectral projector decomposition (`spectralProjector_twoSheet_and_cfc_log`, `gibbsDensityC_strictlyPositive_and_cfc_log`).
    - Proves full noncommutative Umegaki divergence decomposition $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r) - \phi(z)) + D_\phi(z \| \eta_\theta)$ (`umegakiKernel_trace_and_coherence_pythagoras`), isolating the strictly positive off-diagonal coherence defect $\phi(r) - \phi(z) \ge 0$ (vanishing iff $\rho_{01} = 0$), and proving faithfulness ($= 0 \leftrightarrow \rho = \rho_\theta$).
    - Proves entrywise forward Kolmogorov generator ODE: `hasDerivAt_thermalSemigroupC_eq_lindbladian`.
    - Proves strict open-Bloch-ball invariance and positivity preservation for $t \ge 0$ (`thermalSemigroupC_preserves_blochBall`), with exact forward-positivity monoid characterization and backward-time failure witness for every $t < 0$ (`forward_monoid_positivity_iff_and_backward_aporia`).
    - Proves three-channel KMS Spohn entropy production rate $-\mathrm{Re}\mathrm{Tr}(\mathcal{L}(\sigma)(\log\sigma - \log\rho_\theta)) = \sigma_{\mathrm{KMS}}(\gamma, \theta, \sigma) \ge 0$ with strictly positive dissipation whenever off-diagonal coherence $\sigma_{01} \ne 0$ (`operator_spohn_rate_and_strict_coherent_dissipation`).
    - Proves full-matrix Spohn derivative identity $\frac{d}{dt} D_{\mathrm{Umegaki}}(\rho(t) \| \rho_\theta) = -\sigma_{\mathrm{KMS}}(\rho(t))$ and asymptotic global relaxation to the Gibbs state (`master_bloch_umegaki_spohn_and_gibbs_relaxation`).
    - Bridges the Schrödinger GKSL generator on general matrix algebra $M_n(\mathbb{C})$ to the continuous linear map exponential flow `gkslFlow H V t`, proving flow semigroup property (`gkslFlow_add`), orbit derivative ODE (`hasDerivAt_gkslFlow_orbit`), full matrix real trace conservation (`realTrace_gkslFlow`), and Picard–Lindelöf ODE uniqueness (`gkslFlow_unique_of_ode`).
    *Scope boundary*: Finite-matrix Markovian open quantum semigroups; does not claim continuum field-theoretic dissipative Renormalization Group flows.

12. **Doubled Minkowski / Chiral Krein & Circular Split-Octonion Yang–Mills Bridge (`InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge`)**:
    Constructs the typed bridges across the circular split-octonion Peirce basis (`SplitOctonionEllCircularPeirceBasis`), the real doubled chiral Krein frame (`RealDoubledChiralKreinFrame`), the double-Minkowski Pauli soldering (`SplitOctonionDoubleChiralSolderingBridge`), the operator-valued Peirce tetraktys (`TetraktysZornYangMillsBridge`), exterior-algebra self-dual Yang–Mills (`SelfDualConnectionCurvatureYangMillsBridge`), and inductive star-ring colimits (`TwoSheetedYangMillsInductiveColimit`):
    - **Doubled Carrier & Metric Soldering**: Explicit linear equivalences `circularCoordToKreinFrame : Coordinate ≃ₗ[ℝ] KreinFrame4` and `zornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4` transporting the 8 circular Peirce vectors onto `±plusFrame`/`±minusFrame`, proving `chiralKreinForm v v = 2 * wittNorm v` and equating half `chiralKreinForm` simultaneously with `wittNorm`, `(1,3) ⊕ (3,1)` Minkowski norm difference, and the determinant difference of `pauliSolder2x2` (`doubledMinkowski_krein_pauli_soldering_bridge`), alongside uniqueness of `dualConnectionWithMetric minkowskiEta4` (`minkowski_dualConnection_unique`).
    - **Chiral Projectors, Grading & Sheet Flip**: Proves `zornToKreinFrame` intertwines `leftMultiplication uPlus`, `uMinus`, and `lUnit` with `leftChiralProjector`, `rightChiralProjector`, and `chirality` (`gamma5`), and intertwines `signedKappa` with `sheetFlip` (`etaChiral`).
    - **Noncommutative Weyl Channels & Operator Tetraktys**: Realizes the upper/lower circular channels as noncommuting $2 \times 2$ complex Weyl matrices (`weylUpperMat`, `weylLowerMat`), proves exact ordered products in terms of `wittNorm`, `chiralBoostVec`, and `chiralVorticityVec` (`weylChannel_commutator_eq_vorticity`, with explicit noncommuting two-sheet witness `weylChannel_noncomm_sheet_blocks_witness`), and embeds them into `SheetAlgebra (Fin 2 → ℂ)` (`circularSheet_tetraktys_table`).
    - **4×4 Connection, Curvature Action & Colimit Transport**: Specializes `circularGaugeConnection4 ω` to `circularConnectionMat4 x` on scalar 0-forms (`circularGaugeConnection4_evalScalar`), instantiates `peirce_defect_connection_curvature_and_yang_mills_bridge` (`circularGaugeConnection4_yang_mills_bridge`), proves the exact curvature trace (`4 * wittNorm x`), Hilbert–Schmidt action `4 * (wittNorm x ^ 2 + normSq3 (chiralBoostVec x) + normSq3 (chiralVorticityVec x))`, cross-sheet real pontryagin-type cancellation `circularCurvatureMat4_square_trace`, non-Abelian vorticity gap `8 * normSq3 (chiralVorticityVec x)` (`circularCurvatureMat4_vorticity_action_gap`), and star-ring inductive-colimit transport along `InductiveStarColimitCone` (`circularConnection_starColimit_transport`).
    *Scope boundary*: Finite-dimensional, Krein-bilinear, exterior-algebra, and star-ring inductive-colimit theorems; does not claim smooth 4-manifold gauge-bundle PDE existence, analytic continuum limit convergence as $a \to 0$, or existence of a nonzero differential `d` satisfying `matrixExteriorDerivative d A = peirceGradingDeriv P A`.

13. **Canonical Doubled Minkowski / Circular Peirce Self-Dual Yang–Mills & Gauge–Higgs Synthesis (`InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills`)**:
    Bridges the canonical `KreinFrame4`, `CanonicalZorn`, `SheetAlgebra (Fin 2 → ℂ)`, `ExteriorAlgebra ℂ (Fin 4 → ℂ)`, Bogomolnyi energy/topological bounds, and `CanonicalTwoSheetedInductiveColimit.tailTowerCone` on their actual carriers (`propext`, `Classical.choice`, `Quot.sound` only):
    - **Doubled Carrier & Metric Pullback**: Constructs linear equivalences `circularZornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4` (`circularZornToKreinFrame_frame_blocks`, `circularZornToKreinFrame_intertwines_kappa_sheetFlip`, `circularZornToKreinFrame_intertwines_peirce_chirality`) and parity-twisted `lorentzCircularZornToKreinFrame`, proving exact bilinear/quadratic pullback `chiralKreinForm (lorentzCircularZornToKreinFrame X) (lorentzCircularZornToKreinFrame Y) = circularPeircePolar (coordinateEquiv X) (coordinateEquiv Y)` and `2 * wittNorm (coordinateEquiv X)` (`chiralKreinForm_lorentzCircularZornToKreinFrame`), plus `minkowskiEta13_metric_and_dualConnection`.
    - **Chiral Weyl Representations & Peirce Channel Mapping**: Constructs `kreinChiralPlusWeyl`, `kreinChiralMinusWeyl`, off-diagonal `kreinSheetRep`, and `4 × 4` block bispinor `kreinBispinorRep`, proving explicit `sheetFlip`/`chirality` and `doubleMinkowskiSolder` determinant difference compatibility (`kreinChiralWeyl_chirality_and_sheetFlip`), exact Peirce projector/annihilator actions `conePlus`/`coneMinus` on all 8 circular Peirce vectors (`circularSheetRep_peirce_channels`), noncommutativity `[σ⁺(e₁), σ⁻(e₂)] ≠ 0`, and `Tr(kreinBispinorRep u * kreinBispinorRep v) = 2 * chiralKreinForm u v` (`kreinBispinorRep_metric_trace_and_noncomm`).
    - **Gauge–Higgs Splitting, Non-Abelian Self-Dual Yang–Mills Solution, & Bogomolnyi Saturation**: Defines `twoSheetKreinConnection AL AR u` with `Cl(1,1)` parity separation (`twoSheetKreinConnection_curvature_and_parity_split`), builds the `ExteriorAlgebra ℂ (Fin 4 → ℂ)` circular helicity connection `helicityCircularConnection4` and complex chiral Hodge star `chiralHodgeStar4` (`hodgeStar4_sq_on_blades`), proves a genuine non-Abelian self-dual Yang–Mills solution (`F ≠ 0`, `F 0 0 ≠ F 2 2`, `isSelfDualCurvature chiralHodgeStar4 F`, `covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F) = 0`) in `helicityCircularConnection4_solves_self_dual_yang_mills`, proves the 3-way Bogomolnyi action identity `twoSheetBogomolnyi_action_identity`, and transports `kreinBispinorRep u` through star-preserving ring homs and `tailTowerCone` (`kreinBispinorRep_colimit_transport`, synthesized in `master_doubled_minkowski_circular_peirce_yang_mills`).
    *Scope boundary*: Finite-dimensional Krein-bilinear, matrix operator-algebra, exterior-algebra, and star-ring inductive-colimit results only; does not claim smooth 4-manifold gauge-bundle PDE existence, analytic continuum limit convergence as $a \to 0$, or continuum Wightman Yang–Mills mass gaps.

## Causal order and scope boundary

```text
associative-ring idempotency defect (established: PeirceDefectBridge)
  → idempotent Peirce split and ordered boundary cycles (established: PeirceSpine)
  → even/odd defect identity and matrix witness (established: PeirceDefectBridge, PeirceDefectMatrixWitness)
  → Solve et Coagula 5-stage causal compilation chain EC1 ≺ … ≺ EC5 (established: SolveEtCoagulaPeirceAporiaPoset)
  → bipartite separability vs. Peirce defect separation (established: BipartiteSeparabilityAndPeirceEntanglement)
  → Peirce Maurer–Cartan curvature & ExteriorAlgebra matrix Yang–Mills bridge (established: SelfDualConnectionCurvatureYangMillsBridge)
  → M_8(ℝ) real freeze, U(1) BdG circle & custodial twin all-loop vanishing (established: CustodialTwinLoopAndJosephsonLattice)
  → lattice gauge Elitzur vanishing & N-link Wilson string perimeter law (established: ElitzurLatticeGaugeProjection, NLinkElitzurChainAndCompactU1Gauge)
  → Euclidean lattice transfer semigroup, spectral mass gap & OS reflection positivity (established: OsterwalderSchraderTransferSemigroupAndMassGap)
  → trace/adjoint positivity & polygon Lucas coercivity in Limit (established: PeirceTetraktysColimitCoercivity)
  → two-sheet Krein stage & filtered-colimit Peirce bridge (established: TwoSheetKreinStageSystem)
  → infinite-dimensional Cantor boundary Hilbert sewing & anomaly cancellation (established: ConcreteHilbertSewnAnomaly)
  → noncommutative Weyl–Cartan split & Iwasawa KAN / polar equivariance (established: NoncommutativeWeylCartanKANPolarEquivariance, WeylTraceKANPolarEquivariance)
  → off-diagonal Bloch-ball Umegaki relative entropy & quantum Spohn dissipation (established: BlochBallUmegakiAndQuantumSpohn, SchrodingerGKSLFlowBridge)
  → doubled Minkowski/Krein circular split-octonion Weyl connection, curvature action & colimit bridge (established: DoubledMinkowskiCircularChiralYangMillsBridge)
  → canonical Krein–circular Peirce Weyl connection, non-Abelian self-dual Yang–Mills & Bogomolnyi synthesis (established: DoubledMinkowskiCircularPeirceYangMills)
```

In particular, a nonzero `genV` proves failure of Peirce-projectability for the
given operator. As proved in `BipartiteSeparabilityAndPeirceEntanglement`, single-cut
Peirce defect is mathematically decoupled from bipartite tensor entanglement: product
states can have nonzero `genV`, while entangled states also exhibit reduced state
idempotency defect. Establishing continuum 4D quantum Yang–Mills with a mass gap,
continuous $L^2(\mathbb{R})$ Bourgain–Dyatlov FUP, and HTTP 404 Drive doc recovery
remain active open frontiers.

## Worktree and verification boundary

The staged operator-algebra modules and audits were checked with the locked
build command for `PeirceDefectBridgeAudit`, `TwoStateSandwichAudit`, the
`PeirceSpine` umbrella, `Unipotent`, and `PeirceDefectMatrixWitness`; all
targets passed. The imported closure emitted existing linter warnings in
other files. Axiom reports for the new bridge declarations list `propext`;
the separate complementary pairing also uses `Classical.choice` and
`Quot.sound`. The staged proof-proxy gates and OpenGauss screener passed.
`semantic_vacuity_gate.py` reported two `trivial_surface` warnings in older
Steinberg declarations in `Unipotent.lean`; it reported zero findings in the
new Peirce bridge. These checks establish the reported finite ring identities
and tower results only, not the unproved carrier maps above.

## Source map

- `lean/InfoGeometry/Core/IdempotentGraphGrassmannian.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/DefectParity.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceDefectBridge.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceDefectMatrixWitness.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TwoStateSandwich.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/DefectTower.lean`
- `lean/InfoGeometry/Categorical/TwoSheetKreinFilteredColimit.lean`
- `lean/InfoGeometry/Categorical/TwoSheetKreinStageSystem.lean`
- `lean/InfoGeometry/Canonical/SelfDualConnectionCurvatureYangMillsBridge.lean`
- `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`
- `docs/YANG_MILLS_NATIVE_GAUGE_CONTRACT.md`
- `docs/PEIRCE_OPERATOR_ARCHETYPES.md`
- `lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/BipartiteSeparabilityAndPeirceEntanglement.lean`
- `lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/CustodialTwinLoopAndJosephsonLattice.lean`
- `lean/InfoGeometry/OperatorAlgebra/ElitzurLatticeGaugeProjection.lean`
- `lean/InfoGeometry/OperatorAlgebra/NLinkElitzurChainAndCompactU1Gauge.lean`
- `lean/InfoGeometry/OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean`
- `lean/InfoGeometry/OperatorAlgebra/SolveEtCoagulaPeirceAporiaPoset.lean`
- `lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean`
- `lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean`
- `lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean`
- `lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean`
- `src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean`
- `lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean`
- `lean/InfoGeometry/Lie/DoubledMinkowskiCircularChiralYangMillsBridge.lean`
- `src/InfoGeometry/Lie/DoubledMinkowskiCircularChiralYangMillsBridge.lean`
- `tests/lean/InfoGeometry/Lie/DoubledMinkowskiCircularChiralYangMillsBridgeTest.lean`
- `lean/InfoGeometry/Canonical/DoubledMinkowskiCircularPeirceYangMills.lean`
- `src/InfoGeometry/Canonical/DoubledMinkowskiCircularPeirceYangMills.lean`
