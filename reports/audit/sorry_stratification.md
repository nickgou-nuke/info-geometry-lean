# ⚖️ Pauli Authority Audit: Graph Vacuity Stratification

> **Protocol:** Truth lives in Lean; structure lives in the graph.
> **Snapshot:** 28536 theorems analysed via graph-topology evidence.
> **Authority order:** Lean kernel truth > DAG topology > heuristic telemetry.

## Classification Summary

| Class | Count | % |
| :--- | ---: | ---: |
| isolated_theorem | 18389 | 64.4% |
| type_only_theorem | 12 | 0.0% |
| thin_forwarder | 0 | 0.0% |
| supported_theorem | 8522 | 29.9% |
| capstone_endpoint | 0 | 0.0% |
| load_bearing | 1613 | 5.7% |

**Topology-weak surfaces (isolated + type-only + thin-forwarder):** 18401 (64.5%)

## 🗑️ Isolated Theorems (Highest Pruning Priority)
| Theorem | SCC Mass | Depth | File |
| :--- | :---: | :---: | :--- |
| `InfoGeometry.Algebra.PrimeA1RootSystem.all_prime` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean:18` |
| `InfoGeometry.Algebra.PrimeA1RootSystem.mk.inj` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean:0` |
| `InfoGeometry.Algebra.PrimeA1RootSystem.mk.sizeOf_spec` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean:0` |
| `InfoGeometry.Algebraic.Cartan.CartanAutomorphyFactor.map_mul` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:31` |
| `InfoGeometry.Algebraic.Cartan.CartanAutomorphyFactor.map_one` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:30` |
| `InfoGeometry.Algebraic.Cartan.CartanAutomorphyFactor.mk.inj` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:0` |
| `InfoGeometry.Algebraic.Cartan.CartanAutomorphyFactor.mk.sizeOf_spec` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:0` |
| `InfoGeometry.Algebraic.Cartan.CartanRotorCocycle.map_mul` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:74` |
| `InfoGeometry.Algebraic.Cartan.CartanRotorCocycle.map_one` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:73` |
| `InfoGeometry.Algebraic.Cartan.CartanRotorCocycle.mk.inj` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:0` |
| `InfoGeometry.Algebraic.Cartan.CartanRotorCocycle.mk.sizeOf_spec` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/CartanCocycle.lean:0` |
| `InfoGeometry.Algebraic.Cartan.MatrixAutomorphyFactor.map_mul` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean:26` |
| `InfoGeometry.Algebraic.Cartan.MatrixAutomorphyFactor.map_one` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean:25` |
| `InfoGeometry.Algebraic.Cartan.MatrixAutomorphyFactor.mk.inj` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean:0` |
| `InfoGeometry.Algebraic.Cartan.MatrixAutomorphyFactor.mk.sizeOf_spec` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean:0` |
| `InfoGeometry.Algebraic.ChiralAutomorphyFactor.map_mul` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/RealModularReadout.lean:224` |
| `InfoGeometry.Algebraic.ChiralAutomorphyFactor.map_one` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/RealModularReadout.lean:223` |
| `InfoGeometry.Algebraic.ChiralAutomorphyFactor.mk.inj` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/RealModularReadout.lean:0` |
| `InfoGeometry.Algebraic.ChiralAutomorphyFactor.mk.sizeOf_spec` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/RealModularReadout.lean:0` |
| `InfoGeometry.Algebraic.ChiralAutomorphyFactor.pullback.congr_simp` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/RealModularReadout.lean:0` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.canonical_chiralParity` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:75` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.canonical_leftChiralCharge` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:88` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.canonical_modularBoost` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:81` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.canonical_modularHamiltonian` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:102` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.canonical_rightChiralCharge` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:95` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.canonical_root_laws` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:112` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.mk.inj` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:0` |
| `InfoGeometry.Algebraic.ChiralOperatorAlgebra.mk.sizeOf_spec` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean:0` |
| `InfoGeometry.Algebraic.ChiralOperatorCarrier.boost_eps_anticomm` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean:39` |
| `InfoGeometry.Algebraic.ChiralOperatorCarrier.boost_sq` | 0 | 0 | `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean:38` |

## 💎 Load-Bearing Spire (The Spire's Backbone)
| Theorem | Downstream Mass | Transitive Reach | Depth |
| :--- | :---: | :---: | :---: |
| `InfoGeometry.Algebraic.ChiralPhase.ext` | 0 | 0 | 0 |
| `InfoGeometry.Algebraic.ProjectiveReadoutShadow.cocycle_shadow` | 0 | 0 | 0 |
| `InfoGeometry.Algebraic.SplitSignature.splitCliffordVector_sq` | 0 | 0 | 0 |
| `InfoGeometry.Algebraic.SplitSignature.splitQuadraticForm_apply` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.deriv_logSumExpPartition` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.hasDerivAt_logSumExpMoment1` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.hasDerivAt_logSumExpPartition` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.logSumExp_deriv_eq_ratio` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.logSumExp_sum_pos` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.softmaxDist_prob_eq` | 0 | 0 | 0 |
| `InfoGeometry.Analytic.softmaxMean_eq_logSumExpMean` | 0 | 0 | 0 |
| `InfoGeometry.Application.STUOperator.drazinCoreProjector_idempotent` | 0 | 0 | 0 |
| `InfoGeometry.Applications.PrimeKreinKMSBridge.PrimeKreinKMSBridgeData.beta_consistency` | 0 | 0 | 0 |
| `InfoGeometry.Architecture.CartanInvolution.involutive` | 0 | 0 | 0 |
| `InfoGeometry.Architecture.SymmetricPair.K_eq_fixedSubgroup` | 0 | 0 | 0 |
| `InfoGeometry.Architecture.cartanSymmetry_fixpoint` | 0 | 0 | 0 |
| `InfoGeometry.Architecture.cartanSymmetry_involutive` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.ArithmeticExponentialRay.partition_pos` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.BRSTCriticalLineGate.certificate` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.LFunction.UnifiedHorizonWitness.horizonIff` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.prime_mem` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimeBitWittenIndex.finite_witten_index_cancel` | 0 | 0 | 5 |
| `InfoGeometry.Arithmetic.PrimeBitWittenIndex.mobius_eq_zero_of_not_squarefree` | 0 | 0 | 5 |
| `InfoGeometry.Arithmetic.PrimeBitWittenIndex.mobius_prime_product_eq_parity` | 0 | 0 | 5 |
| `InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.eps_sq_zero` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimeMajoranaCAR.ExteriorCARPair.iota_sq_zero` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.RealMajoranaWittenIndexGate.certificate` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice.bitEnergy_eq_log_bitInteger` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice.primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy` | 0 | 0 | 0 |
| `InfoGeometry.Arithmetic.PrimitiveProjectiveRays.finiteArithmeticNormalizedRay_scale_counts` | 0 | 0 | 0 |

## Interpretation

- **isolated_theorem:** Zero transitive downstream reach. Formal vacuity confirmed.
- **load_bearing:** High causal mass. Removal would collapse significant theory volume.
- **capstone_endpoint:** Deep theorems (Depth > 4) with zero users. Intentional milestones.
