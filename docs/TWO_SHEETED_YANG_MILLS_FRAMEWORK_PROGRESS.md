# Two-Sheeted Yang–Mills Framework Progress

Status reviewed: 2026-10-31 against `HEAD` `5ef9727eb427d4043cae6f8d09992816064a871a` and the staged worktree.

This note documents the established operator-algebraic Peirce defect spine and
its kernel-checked bridges to matrix exterior-algebra Yang–Mills connection
curvature (`SelfDualConnectionCurvatureYangMillsBridge`), the finite-stage
two-sheet Hestenes–Krein stage system and its filtered colimit
(`TwoSheetKreinStageSystem`), and the `Cl(1,1)^{\otimes n}` inductive colimit
`Limit` (`PeirceTetraktysColimitCoercivity`), while strictly separating these
proved algebraic and trace-extension theorems from unproved continuum 4D
quantum Yang–Mills PDE/Wightman mass-gap claims or multipartite entanglement
claims.

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

## Causal order and scope boundary

```text
associative-ring idempotency defect (established: PeirceDefectBridge)
  → idempotent Peirce split and ordered boundary cycles (established: PeirceSpine)
  → even/odd defect identity and matrix witness (established: PeirceDefectBridge, PeirceDefectMatrixWitness)
  → Peirce Maurer–Cartan curvature & ExteriorAlgebra matrix Yang–Mills bridge (established: SelfDualConnectionCurvatureYangMillsBridge)
  → trace/adjoint positivity & polygon Lucas coercivity in Limit (established: PeirceTetraktysColimitCoercivity)
  → two-sheet Krein stage & filtered-colimit Peirce bridge (established: TwoSheetKreinStageSystem)
```

In particular, a nonzero `genV` proves failure of Peirce-projectability for the
given operator. Calling it quantum entanglement requires a separately specified
tensor factorization and a separability theorem relative to that factorization.

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
