# Unified Leibniz–Derivation–Fréchet–Onsager Architecture Map

> Status: `current authority`
> Source reviewed: 2026-11-22 at `a7e91ecfcdb84f19a9da7a4160d670e5589c89c4` (all M1–M5 bridge, capstone, and audit modules compiled cleanly via locked Lake build, M5 `.lean` modules passed `-DwarningAsError=true`, kernel axiom audits passed, and `Canonical/All.lean` wired for static reachability)
> Toolchain & Mathlib pin: Lean `v4.34.1` ([`lean-toolchain`](../lean-toolchain)), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` ([`lake-manifest.json`](../lake-manifest.json))
> Umbrella owners: [`lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean`](../lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean), [`lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean`](../lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean)

---

## 1. Overview & Four-Pillar Spine

This architecture map documents the unified Lean 4 framework connecting the four previously disconnected repository ontology pillars—`Leibniz`, `Derivation`, `Fréchet`, and `Onsager`—via additive, diamond-free bridges closing **Gaps A, B, C, and D**, synthesized in [`InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone`](../lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean) and wired into [`lean/InfoGeometry/Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean).

1. **Pillar I — `Leibniz`:** Nonassociative algebraic derivation law `IsLeibniz R A D` (`D (x * y) = D x * y + x * D y`) and Lie algebra `derivations R A` ([`Algebra/NonAssocDerivation.lean`](../lean/InfoGeometry/Algebra/NonAssocDerivation.lean)), arbitrary-degree Chevalley–Eilenberg DGA (`ceExteriorDerivative`, `d² = 0`, `ceWedge`, `ceCurvature`, `ceCurvature_eq`) in [`OperatorAlgebra/DerivationExteriorCalculus.lean`](../lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean) and [`OperatorAlgebra/DerivationDifferentialForms.lean`](../lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean), Peirce $\mathbb{Z}_2$ superderivations ([`OperatorAlgebra/PeirceGradedSuperderivations.lean`](../lean/InfoGeometry/OperatorAlgebra/PeirceGradedSuperderivations.lean)), and braided derivations ([`Canonical/BraidedDerivation.lean`](../lean/InfoGeometry/Canonical/BraidedDerivation.lean)).
2. **Pillar II — `Derivation`:** Faithful derivation Lie lanes `DerivationLieLane R A` and faithfulness-free `LieActionLane R A` ([`Algebra/DerivationLieLane.lean`](../lean/InfoGeometry/Algebra/DerivationLieLane.lean), [`Algebra/DerivationLieLaneRepresentation.lean`](../lean/InfoGeometry/Algebra/DerivationLieLaneRepresentation.lean)), Maurer–Cartan tower ([`OperatorAlgebra/MaurerCartanTower.lean`](../lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean)), Peirce cut inner derivations `cutDerivation` ([`Canonical/PeirceFrechetOperatorArchetypes.lean`](../lean/InfoGeometry/Canonical/PeirceFrechetOperatorArchetypes.lean)), plus the 39 consolidated `*Derivation` lanes across `Modular/*`, `G2Derivation`/`JordanDerivation`/Zorn, and super/braided systems (Gap D).
3. **Pillar III — `Fréchet`:** Continuous operator derivations `FrechetOperatorDerivation` ([`Optics/OperatorDerivationForms.lean`](../lean/InfoGeometry/Optics/OperatorDerivationForms.lean)), Fréchet exterior forms `OperatorFrechetFormK` / `RealOperatorFrechetForm`, `frechetExtDeriv` / `frechetExtDerivReal`, `SmoothOpMap`, `frechetVectorFieldDerivationLane`, `frechetExtDeriv_logPartition_bkmHessian_alignment` ([`Canonical/OperatorFrechetForms.lean`](../lean/InfoGeometry/Canonical/OperatorFrechetForms.lean)), cyclic Gibbs differentiation `hasFDerivAt_logTracedExponential` ([`Canonical/NoncommutativeGibbsExpectationCyclicDerivative.lean`](../lean/InfoGeometry/Canonical/NoncommutativeGibbsExpectationCyclicDerivative.lean)), and trajectory-level Fréchet chain-rule Second Laws (Gap C).
4. **Pillar IV — `Onsager`:** `OnsagerCasimirSystem`, `TimeReversal`, `ParityOnsagerSystem` ([`Thermo/OnsagerOperatorClosure.lean`](../lean/InfoGeometry/Thermo/OnsagerOperatorClosure.lean)), arbitrary-degree `OnsagerFormPairing` / `ParityOnsagerFormPairing` ([`Thermo/OnsagerDifferentialFormsBridge.lean`](../lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean)), `SuperMetriplectic` Cartan/Schur/Drazin/TKK/Conformal blocks ([`SuperMetriplectic/Axioms.lean`](../lean/InfoGeometry/SuperMetriplectic/Axioms.lean), [`Blocks.lean`](../lean/InfoGeometry/SuperMetriplectic/Blocks.lean), [`CartanBridge.lean`](../lean/InfoGeometry/SuperMetriplectic/CartanBridge.lean)), finite CE–BKM systems ([`Canonical/CEBKMOnsagerSystem.lean`](../lean/InfoGeometry/Canonical/CEBKMOnsagerSystem.lean), [`CEBKMOnsagerGibbsIntegration.lean`](../lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsIntegration.lean), [`CEBKMOnsagerGibbsNOperatorFamily.lean`](../lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean), [`ErlangenOperator2Bridge.lean`](../lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean)), and `matrixKuboMoriMobility` ([`Canonical/BKMOnsagerMobilityBridge.lean`](../lean/InfoGeometry/Canonical/BKMOnsagerMobilityBridge.lean)).

### Proved vs. Conditional/Open Classification (Bucket 1 / 2 / 3)

| Pillar | Bucket 1 (Unconditional Algebraic / Kernel Identities) | Bucket 2 (Conditional / Finite-Dim / Supplied-Hypothesis Results) | Bucket 3 (Open / External Beyond Current Scope) |
|---|---|---|---|
| **Leibniz** | Arbitrary-degree CE DGA, $d^2 = 0$, graded wedge `ceWedge`, `ceCurvature_eq` (`DerivationDifferentialForms.lean:561`), Ricci/Bianchi, commutative `deRhamComplex` algebraic laws. | `derivationDeRhamComplex` supplies `hodge`, `hkOperator`, `hk_sq_zero` as parameters; upstream `BraidedDerivation.HomogeneousElement` lacks grade membership (`BraidedDerivation.lean:18-35`, closed additively via guarded `GradedBraidedDerivation` in M4B). | Infinite-dimensional analytic Hodge star / Hestenes–Krein construction. |
| **Derivation** | Exact Maurer–Cartan $\theta_L/\theta_R$ sign dictionary; faithful quotient/range factorizations; additive Gap D bridges (`ModularDerivationLaneBridge`, `ExceptionalZornSuperBraidedDerivationBridge`). | `TowerDerivation` colimit lift requires cocone density `h_surj` & eventual injectivity `h_inj`; `LocalDerivationSystem` injectivity requires `hinj`; `ScalarDerivation F` equivalence requires `[CommRing F]`. | Global infinite-stage direct-limit gauge connection beyond stagewise `TensorStageExactConnection`. |
| **Fréchet** | Linear CE alignment `frechetExtDerivK_linear_eq_ceExteriorDerivative` for `ContDiff 𝕜 ⊤` `SmoothOpMap`; typed disambiguation of `OperatorFrechetJet` vs. alternating `OperatorFrechetForm`. | $d_{\mathrm{Fr}}^2 = 0$ assumes `ContDiff`/`minSmoothness`; Duhamel alignment requires `[CompleteSpace A]`; finite Gibbs BKM alignment holds on `FiniteOperatorAlgebra n` with `tracedExponential H ∈ Complex.slitPlane`; Gap C Second Law is conditioned on supplied differentiable `HasDerivAt` trajectories. | Infinite-dimensional KMS/BKM Fréchet exterior calculus; internal Picard–Lindelöf nonlinear ODE existence solver for $H'(t) = -i[H_{\mathrm{eq}}, H] - K_{D_H}(\rho_H - \sigma)$. |
| **Onsager** | Reciprocity & parity pairing on `ActionOperatorForm`, `DerivationOperatorForm`, and `OpForm`; concrete finite Gibbs parity (`star` and `τ`); Peirce `cutDerivation` Cartan split. | `FaithfulDensityOperator.bkmOnsagerForm` (`SouriauOnsagerBKMRealForm.lean:114`) takes explicit `h_nonneg` (discharged in `NoncommutativeGibbsBKMHessianBridge.lean:235`); `ScalarSchurDrazinBlock` / `TKKOnsagerMatrix` / `DrazinCartanOnsagerBridge` Onsager systems take explicit PSD / `0 ≤ effectiveEvenOnsager` / `bodyForce ≠ 0` hypotheses. | Infinite-dimensional KMS/BKM Duhamel integral existence without finite-dim/boundedness hypotheses. |

---

## 2. Closed Gaps A, B, C, and D

### 2.1 Gap A — `SuperMetriplectic` Cartan–Schur–Drazin & Peirce `cutDerivation`
- **Bridge Owners:**
  - [`lean/InfoGeometry/SuperMetriplectic/CartanOnsagerParityBridge.lean`](../lean/InfoGeometry/SuperMetriplectic/CartanOnsagerParityBridge.lean) (+ [`...Audit.lean`](../lean/InfoGeometry/SuperMetriplectic/CartanOnsagerParityBridgeAudit.lean))
  - [`lean/InfoGeometry/SuperMetriplectic/PeirceCutCartanDerivationBridge.lean`](../lean/InfoGeometry/SuperMetriplectic/PeirceCutCartanDerivationBridge.lean) (+ [`...Audit.lean`](../lean/InfoGeometry/SuperMetriplectic/PeirceCutCartanDerivationBridgeAudit.lean))
  - Aggregated in [`lean/InfoGeometry/SuperMetriplectic/All.lean`](../lean/InfoGeometry/SuperMetriplectic/All.lean).
- **Verified Upstream Owner Locations:**
  - `ScalarSchurDrazinBlock`, `effectiveEvenOnsager`, `drazinDefectProjector`, `BodyEntropyProduction`, and `DrazinPenroseSchurTriad` reside in [`lean/InfoGeometry/SuperMetriplectic/Axioms.lean`](../lean/InfoGeometry/SuperMetriplectic/Axioms.lean) (there is no `ScalarSchurDrazinBlock.lean`).
  - `TKKGrade`, `TKKOnsagerMatrix`, `ConformalOnsagerBlock`, and `ConformalPKMetriplecticSplit` reside in [`lean/InfoGeometry/SuperMetriplectic/Blocks.lean`](../lean/InfoGeometry/SuperMetriplectic/Blocks.lean).
  - `DrazinCartanOnsagerBridge` resides in [`lean/InfoGeometry/SuperMetriplectic/CartanBridge.lean`](../lean/InfoGeometry/SuperMetriplectic/CartanBridge.lean).
- **Constructed Bridges & Boundaries:**
  - `cartanTimeReversal` (`-S.θ`, making $\mathfrak{p}$ $T$-even and $\mathfrak{k}$ $T$-odd) and `cartanInvolutionTimeReversal` (`S.θ`) realize `TimeReversal L`, upgrading `CartanOnsagerSplit L` and `DrazinCartanOnsagerBridge` (with PSD/probe & $\mathfrak{k}\leftrightarrow\mathfrak{p}$ skew forms) to `ParityOnsagerSystem`.
  - `scalarEffectiveOnsagerSystem` / `scalarEffectiveParityOnsagerSystem` (`0 ≤ B.effectiveEvenOnsager`), `triadEffectiveOnsagerSystem` / `triadEffectiveParityOnsagerSystem` (`T.entropy.bodyForce ≠ 0`), `tkkParityOnsagerSystem`, and `conformalBlockCanonicalParityOnsagerSystem` bridge every `SuperMetriplectic` block into `OnsagerCasimirSystem` and `ParityOnsagerSystem`.
  - `peirceSymmetricLieAlgebra P` (`invS P = 2 • P - 1`) establishes exact submodule equalities `LinearMap.ker (peirceAdMap P ∘ₗ peirceAdMap P) = S.𝔨` (`peirceAdSq_ker_eq_k`) and `LinearMap.range (peirceAdMap P) = S.𝔭` (`peirceAd_range_eq_p`), constructs `peirceCartanOnsagerSplit P`, `peirceCartanLinearEquiv P`, `peirceCutDerivationLieLane n : DerivationLieLane ℝ (FiniteOperatorAlgebra n)`, and `peirceDerivCartanOnsagerSplit P` (`cutStabilizer P = evenLieSubalgebra`).

### 2.2 Gap B — Concrete BKM Parity Reciprocity & Arbitrary-Degree Unification
- **Bridge Owner:** [`lean/InfoGeometry/Canonical/CEBKMParityUnificationBridge.lean`](../lean/InfoGeometry/Canonical/CEBKMParityUnificationBridge.lean) (+ [`...Audit.lean`](../lean/InfoGeometry/Canonical/CEBKMParityUnificationBridgeAudit.lean)).
- **Verified Upstream Owner Location Note:** `ceCurvature_eq` resides in [`lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean`](../lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean) (`L561`, namespace `InfoGeometry.OperatorAlgebra.DerivationDifferentialForms`), not `DerivationExteriorCalculus.lean`.
- **Critical `star` Anti-Automorphism vs. `*`-Automorphism `τ` Sign Boundary:**
  - `starDerivationTimeReversal` (`star (X * Y) = star Y * star X`) satisfies `[star X, star Y] = - star [X, Y]`, so `ceCurvatureBKMProbeForm_starDerivation_eq` reflects `Q` to `- star Q`; hence `ceCurvatureBKMProbeForm` is $T$-odd precisely for **`IsSelfAdjoint Q`**. Moreover, `logPartitionOneForm_finiteGibbs_star_unification_reversible_eq_zero` proves that when `A₁`, `A₂`, and `Q` are all self-adjoint, `[A₁, A₂]` is anti-self-adjoint and `PS.reversible x₁ x₂ = 0` identically.
  - By contrast, an involutive `ℝ`-algebra `*`-automorphism `τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n` (`τ² = id`, `τ D.rho = D.rho`, real-trace preserving) preserves brackets (`[τ X, τ Y] = τ [X, Y]`), yielding genuinely non-degenerate $T$-odd reversible curvature when `τ Q = -Q` (`finiteCEParityOnsagerSystemOfAut`, `finiteGibbsCEParityOnsagerSystemOfAut`, witnessed at `n = 2` with `conjStarAlgEquiv 2`, `H = tiltOp2`, `a = switchOp2`, `Q = Complex.I • switchOp2` in `logPartitionOneForm_finiteGibbs_aut_unification_nondegenerate_witness`).
- **Arbitrary-Degree Unification:** Bridges `OperatorFrechetFormK` / `RealOperatorFrechetForm` (`frechetFormToCEForm`, `frechetExtDerivK_linear_eq_ceExteriorDerivative`, `frechetExtDeriv_logPartition_bkmHessian_alignment`) through `DerivationOperatorForm`, `ceExteriorDerivative`, `ceCurvature` / `ceCurvature_eq`, `ParityOnsagerFormPairing`, and `ErlangenOperator2Bridge.gibbsNOperatorFamilyErlangenDatum`.

### 2.3 Gap C — Trajectory-Level Fréchet Chain-Rule Metriplectic Second Law
- **Owners:**
  - [`lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLaw.lean`](../lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLaw.lean) (complementing algebraic [`BKMOnsagerMobilityBridge.lean`](../lean/InfoGeometry/Canonical/BKMOnsagerMobilityBridge.lean)).
  - Non-clobbering Gap C Audit: [`lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean`](../lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean) (66 `#print axioms` checks + `Lean.Util.CollectAxioms` sweep; note that [`BKMMetriplecticTrajectorySecondLawAudit.lean`](../lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawAudit.lean) on `HEAD` belongs to `RegularSupportSecondLaw` per external commit `41d8b01527` and is preserved untouched).
- **Three-Layer Architecture & Boundaries:**
  1. **Layer 1 (Banach `GenericMetriplecticFlow.System`):** `banach_metriplectic_hasDerivAt_nonpos`, `banach_metriplectic_antitoneOn`, `genericMetriplectic_freeEnergy_hasDerivAt_nonpos`, `genericMetriplectic_freeEnergy_antitoneOn` over arbitrary real normed spaces and convex intervals `I`.
  2. **Layer 2 (Finite Gibbs–BKM on `FiniteOperatorAlgebra n`):** `gibbsRelativePotential`, `hasFDerivAt_gibbsRelativePotential_of_isSelfAdjoint` (`[Nonempty (Fin n)]`, `tracedExponential H ∈ Complex.slitPlane`), self-adjointness-preserving `gibbsMetriplecticFlow`, unconditional unitary commutator trace cancellation (`finiteOperatorTrace_gibbsUnitaryVectorField_re_eq_zero`, without `[H_eq, H] = 0`), strict dissipation `deriv_gibbsRelativePotential_metriplectic_neg_of_ne` (`ρ_t ≠ σ`), `kuboMoriTransform_commutator_eq_commutator_rho`, and `hasDerivAt_normalizedExponential`.
  3. **Layer 3 (Primal Matrix Upgrade):** `matrixOfOpCLMℝ` / `matrixOpCLMℝ`, `hasDerivAt_freeEnergy_of_matrixKuboMoriMobility`, `antitoneOn_freeEnergy_of_matrixKuboMoriMobility_of_reversible_orthogonal`, `evolvingGibbsMetriplecticSystem` at `rho t := matrixOfOp (normalizedExponential (H t))`, and `hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory`.
  - **External ODE Boundary:** All trajectory theorems take a supplied differentiable curve `HasDerivAt H ... t` / `HasDerivAt x ... t`; global Picard–Lindelöf nonlinear ODE existence over `(a, b)` remains external. `open scoped Matrix.Norms.L2Operator` is kept strictly section-local in Layer 3.

### 2.4 Gap D — Additive Unification of `*Derivation` Lanes (Complete 39-Entry Catalog)
- **Bridge Owners:**
  - M4A: [`lean/InfoGeometry/Canonical/ModularDerivationLaneBridge.lean`](../lean/InfoGeometry/Canonical/ModularDerivationLaneBridge.lean) (+ [`...Audit.lean`](../lean/InfoGeometry/Canonical/ModularDerivationLaneBridgeAudit.lean))
  - M4B: [`lean/InfoGeometry/Canonical/ExceptionalZornSuperBraidedDerivationBridge.lean`](../lean/InfoGeometry/Canonical/ExceptionalZornSuperBraidedDerivationBridge.lean) (+ [`...Audit.lean`](../lean/InfoGeometry/Canonical/ExceptionalZornSuperBraidedDerivationBridgeAudit.lean))
- **Extension of [`R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md`](R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md) §6:**
  Section 6 of the R1 specification records the 15 Tier 3 adapters (`NonAssocDerivation.IsLeibniz`/`derivations`, `LieActionLane`, `DerivationLieLane`, `AssociativeGaugeConnection.IsLeibniz`, `NonAssocIteratedLeibniz.IsDerivation`, `AlternativeDerivations.NonAssocDerivation`, `NCDerivation`, `NCG.DerivationDifferential.System`/`LieSystem`, `AlgebraDerivation`, `CyclicAlgebraDerivation`, `Modular.ExactSequence.Derivation`, `OperatorAlgebra.ExteriorAlgebra.OpDerivation`, `FormDerivation`, `FrechetOperatorDerivation`, `ThermodynamicOperatorDerivation`). Tables A and B below extend that catalog with all **39** Gap D `*Derivation` lanes unified in M4A and M4B, together with exact morphism strength and guardrails.

#### Table A: M4A — `Modular/*` & Associative / Involutive Wrappers (`ModularDerivationLaneBridge.lean`)

| # | Unconsolidated Type & Owner | Scalar Ring / Carrier Hypotheses | Bridge Symbol(s) in `ModularDerivationLaneBridge` | Morphism Strength & Exact Scope / Guardrail |
|---|---|---|---|---|
| D1 | `Modular.LieIdeal.RingDerivation A` (`Modular/DerivationLieIdeal.lean:17`) | `[Ring A]` (`ℤ`-linear) | `lieIdealRingDerivationEquivDerivations`, `_commutator`, `_isInner_iff` | **Full `≃` (`+`, `⁅·,·⁆`, inner ideal)** into `derivations ℤ A` |
| D2 | `Modular.DualExponential.RingDerivation A` (`Modular/DualExponentialCommutatorBridge.lean:54`) | `[Ring A]` (`ℤ`-linear) | `dualExponentialRingDerivationEquivDerivations`, `_commutator` | **Full `≃` (`+`, `⁅·,·⁆`)** into `derivations ℤ A` |
| D3 | `Modular.LieAlgebra.RingDerivation A` (`Modular/DualFlowLieAlgebraBridge.lean:25`) | `[Ring A]` (`ℤ`-linear) | `lieAlgebraRingDerivationEquivDerivations`, `_commutator` | **Full `≃` (`+`, `⁅·,·⁆`)** into `derivations ℤ A` |
| D4 | `Modular.Synthesis.RingDerivation A` (`Modular/NoncommutativeModularRadonSurprisalBridge.lean:83`) | `[Ring A]` (`ℤ`-linear) | `synthesisRingDerivationEquivDerivations`, `_add_apply`, `_bracket_apply` | **Full `≃` (`+`, `⁅·,·⁆`)** into `derivations ℤ A` |
| D5 | `Modular.FullLieAlgebra.Der R A` (`LieDerivation R A A`) | `[CommRing R] [Ring A] [Algebra R A]` | `derivationsToFullLieDerHom`, `fullLieDerLieActionLane` | **One-way `→ₗ⁅R⁆` + `LieActionLane R A` only** (NOT `≃`; Lie-bracket derivations need not satisfy associative product Leibniz) |
| D6 | `Modular.NoncommutativeRN.NoncommutativeDerivation A` (`Modular/NoncommutativeRadonNikodymDLog.lean:34`) | `[Ring A]` (`ℤ`-linear) | `noncommutativeDerivationEquivDerivations` | **Full `≃`** into `derivations ℤ A` |
| D7 | `Modular.Commutant.Derivation A` (`Modular/CommutantSemidirectProduct.lean:33`) | `[Ring A]` (`ℤ`-linear) | `commutantDerivationEquivDerivations` | **Full `≃`** into `derivations ℤ A` |
| D8 | `Modular.LieIdeal.Derivation A` (`Modular/InnerDerivationLieIdeal.lean:28`) | `[Ring A]` (`ℤ`-linear) | `lieIdealDerivationAddEquivDerivations` | **Full `≃+`** into `derivations ℤ A` |
| D9 | `Modular.TimeSemigroup.Derivation A` (`Modular/ModularTimeSemigroupBridge.lean:35`) | `[Ring A]` (`ℤ`-linear) | `timeSemigroupDerivationEquivDerivations` | **Full `≃`** into `derivations ℤ A` |
| D10 | `Modular.SuperKMS.LinearDerivation R A` (`Modular/SuperKMS.lean:161`) | `[CommRing R] [Ring A] [Algebra R A]` (or `[Ring R] [Ring A] [Module R A]`) | `superKMSLinearDerivationEquivDerivations`, `superKMSLinearDerivationToZDerivations` (`_injective`) | **Full `≃`** into `derivations R A` under `[CommRing R] [Algebra R A]`; **injective-only** into `derivations ℤ A` under `[Ring R]` |
| D11 | `Modular.KMSState.LinearDerivation R A` (`Modular/KMSState.lean:152`) | `[CommRing R] [Ring A] [Algebra R A]` (or `[Ring R]`) | `kmsStateLinearDerivationEquivDerivations`, `kmsStateLinearDerivationToZDerivations` (`_injective`) | **Full `≃`** into `derivations R A` under `[CommRing R] [Algebra R A]`; **injective-only** into `derivations ℤ A` under `[Ring R]` |
| D12 | `Modular.IsLinearDerivation` (`Modular/TrifoldRadonNikodymBridge.lean:277`) | `[CommRing R]`, `D : R →ₗ[R] R` | `trifoldIsLinearDerivationEquivDerivations` | **Full `≃`** (`{ D // IsLinearDerivation D } ≃ derivations R R`) |
| D13 | `Modular.ModularSurprisalDerivationBridge.IsLinearDerivation` (`Modular/ModularSurprisalDerivationBridge.lean:266`) | `[CommRing R]`, `D : R →ₗ[R] R` | `modularSurprisalIsLinearDerivationEquivDerivations` | **Full `≃`** (`{ D // IsLinearDerivation D } ≃ derivations R R`) |
| D14 | `Information.ModularSurprisalDerivationBridge.IsLinearDerivation` (`Information/ModularSurprisalDerivationBridge.lean:176`) | `[CommRing R]`, `D : R →ₗ[R] R` | `infoModularSurprisalIsLinearDerivationEquivDerivations` | **Full `≃`** (`{ D // IsLinearDerivation D } ≃ derivations R R`) |
| D15 | `Modular.SemidirectExterior.Derivation R A` (`Modular/SemidirectExteriorAlgebra.lean:32`) | `[CommRing R] [Ring A] [Algebra R A]` (or `[Ring R]`) | `semidirectDerivationEquivDerivations`, `semidirectDerivationToZDerivations` (`_injective`) | **Full `≃`** (`0`, `⁅·,·⁆`) into `derivations R A` under `[CommRing R]`; **injective-only** into `derivations ℤ A` under `[Ring R]` |
| D16 | `Modular.TrifoldSurprisalIntertwiningBridge.OuterDerivation ι R` (`Modular/TrifoldSurprisalIntertwiningBridge.lean:138`) | `[Fintype ι] [DecidableEq ι] [CommRing R]` (or `[Ring R]`), `Matrix (ι ⊕ ι) (ι ⊕ ι) R` | `outerDerivationToDerivations` (`_injective`), `outerDerivationEquivSubtype`, `outerDerivationToZDerivations` (`_injective`) | **Injective-only** into `derivations R ...` (`≃` onto proper subtype `{ D // D 1 = 0 ∧ D GammaGrading = 0 }`); **injective-only** into `derivations ℤ ...` under `[Ring R]` |
| D17 | `Algebra.DualAlgebra.AlgDerivation R B` (`Algebra/DualAlgebraAutomorphismDerivationBridge.lean:29`) | `[CommRing R] [NonUnitalNonAssocRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]` | `algDerivationEquivDerivations`, `algDerivationToZDerivations` (`_injective`) | **Full `≃`** into `derivations R B` under `[CommRing R]`; **injective-only** into `derivations ℤ B` under `[Ring R]` |
| D18 | `Canonical.OperatorialFierz.OperatorDerivation 𝒜` (`Canonical/OperatorialFierzDerivationBridge.lean:43`) | `[NonUnitalNonAssocRing 𝒜] [Module ℝ 𝒜] [IsScalarTower ℝ 𝒜 𝒜] [SMulCommClass ℝ 𝒜 𝒜]` | `operatorDerivationEquivDerivations` | **Full `≃`** into `derivations ℝ 𝒜` |
| D19 | `EndToEnd.Derivation A` (`EndToEnd.lean:19`) | `[Ring A] [Algebra ℂ A]` | `endToEndDerivationEquivDerivations` | **Full `≃`** into `derivations ℂ A` |
| D20 | `EndToEnd.KMS.ModularDerivation A` (`EndToEnd/KMS.lean:54`) | `[Ring A] [Algebra ℂ A]` | `kmsModularDerivationEquivDerivations` | **Full `≃`** into `derivations ℂ A` |
| D21 | `QuantumGeometry.BerryKeating.ComplexDerivation A` (`QuantumGeometry/BerryKeatingDilationBridge.lean:46`) | `[Ring A] [Algebra ℂ A]` | `complexDerivationEquivDerivations` | **Full `≃`** into `derivations ℂ A` |
| D22 | `Canonical.G2Derivation R V` (`Canonical/AlbertAlgebraGenerationsBridge.lean:232`) | `[Field R] [AddCommGroup V] [Module R V]`, `ExteriorAlgebra R V` | `albertG2DerivationEquivDerivations` | **Full `≃`** into `derivations R (ExteriorAlgebra R V)` |
| D23 | `_root_.Derivation R A A` & `BipolarObservableMetriplecticAlgebra.DerivationFrame A` (`L41`) | `[CommRing R] [CommRing A] [Algebra R A]` (`ℝ` for `DerivationFrame`) | `mathlibDerivationLinearEquivDerivations`, `mathlibDerivationLieEquivDerivations`, `derivationFrameToDerivationsTriple`, `mathlibDerivationLieLane` | **Full `≃ₗ[R]` & `≃ₗ⁅R⁆`** + `DerivationLaneEquiv` |
| D24 | `Modular.ColimitFlowDerivation.TowerDerivation` (`L69`) & `Modular.ColimitKMSInfinitesimal.TowerDerivation` (`L50`) | `A : ℕ → Type*`, `iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)` | `colimitFlowTowerEquivKMSTower`, `colimitFlowStageDerivation`, `colimitFlowTowerToColimitDerivation`, `colimitKMSInfinitesimalToColimitDerivation`, `colimitComplexTowerLieLane` | **Stagewise** into `derivations ℂ (A n)`; **colimit** into `derivations ℂ A_inf` conditioned on cocone density `h_surj` & eventual injectivity `h_inj` (or `δ_inf` extension `h_ext`) |
| D25 | `Modular.ColimitDerivation.LocalDerivationSystem` (`Modular/ModularColimitDerivation.lean:59`) | `[CommRing R]`, directed `A : I → Type*` | `localDerivationStage`, `colimitDerivationToDerivations` (`_injective` under `hinj`), `colimitDerivationLieLane` | **Stagewise** into `derivations R (A i)`; **colimit** into `derivations R (ColimitAlg sys)` (injective under stage-inclusion injectivity `hinj`) |
| D26 | Standalone `[Ring]`/`[NonUnitalNonAssocRing]` wrappers (`OpDerivation`, `CommRingDerivation` ×2, `GenericDerivation`, `Synthesis.Derivation`, `DualExponentialArchitectureCertificate.Derivation`, `PhaseSpace.Derivation`, `GaugeDerivation`) | `[Ring]` / `[CommRing]` / `[NonUnitalNonAssocRing]` | `posetOpDerivationEquivDerivations`, `commRingDerivationEquivDerivations`, `genericDerivationEquivDerivations`, `densityDLogDerivationEquivDerivations`, `synthesisDerivationEquivDerivations`, `dualExpCertDerivationEquivDerivations`, `phaseSpaceDerivationEquivDerivations`, `gaugeDerivationEquivDerivations` | **Full `≃`** into `derivations ℤ` of each carrier |
| D27 | Proper involutive sub-types: `Cuntz.StarDerivation` (`L18`), `Cuntz.InvolutiveDerivation` (`L16`), `KreinInnerDerivation.KreinStarDerivation` (`L68`) | `[Ring A] [StarRing A]` / `sharp : A → A` / `[KreinSpace H]` on `H →L[ℝ] H` | `starDerivationToDerivations` (`_injective`, `≃ starPreservingDerivations A`), `involutiveDerivationToDerivations` (`_injective`), `kreinStarDerivationToDerivations` (`_injective`) | **Injective-only** into `derivations ℤ` (forgetting `star'`/`sharp'`/`kreinStar'`); `≃` onto the respective involution-preserving Lie subalgebra/subtype |
| D28 | `Canonical.CoordinateFreeSouriau.ScalarDerivation F` (`Canonical/CoordinateFreeSouriau.lean:23`) | **`[CommRing F]` required** | `scalarDerivationEquivDerivations` | **Full `≃`** into `derivations ℤ F` **strictly under `[CommRing F]`** (fails Leibniz on noncommutative rings) |

#### Table B: M4B — `G2Derivation`, `JordanDerivation`, Zorn, Super & Braided Lanes (`ExceptionalZornSuperBraidedDerivationBridge.lean`)

| # | Unconsolidated Type & Owner | Carrier & Diamond-Free Strategy | Bridge Symbol(s) in `ExceptionalZornSuperBraidedDerivationBridge` | Morphism Strength & Exact Scope / Guardrail |
|---|---|---|---|---|
| D29 | `G2DerivationLieAlgebra.G2Derivation R` (`Algebra/Zorn/G2DerivationLieAlgebra.lean:79`) | Wrapped `CrossProdCarrier R` (`Fin 7 → R` with `crossProd`; no global `Pi` `Mul` pollution) | `g2DerivationEquivIntDerivations`, `LinearG2Derivation` → `linearG2DerivationEquivDerivations`, `crossProdCarrierDerivationLieLane`, `crossProdCarrierOnsagerSystem` | **Full `≃`** into `derivations ℤ (CrossProdCarrier R)` (no `map_smul` on `G2Derivation R`); **Full `≃`** into `derivations R (CrossProdCarrier R)` for `LinearG2Derivation` (`[CommRing R]`) |
| D30 | `ZornVectorMatrix.Derivation` (`Algebra/ZornVectorMatrix.lean:1932`) | Existing global `NonUnitalNonAssocRing`/`IsScalarTower`/`SMulCommClass` via `ZornDerivationBridge.lean` | `zornVectorMatrixDerivationEquivDerivations`, `zornVectorMatrixDerivationLieLane`, `zornVectorMatrixOnsagerSystem` | **Full `≃`** into `derivations R (ZornVectorMatrix R)` (`[CommRing R]`) + `DerivationLieLane` + `OnsagerCasimirSystem` |
| D31 | `G2ToBraidChain.G2Derivation` (`L55`), `BaezG2SplitOctonion.SplitCayleyG2Derivation` (`L175`), `RealSplitOctonionDerivation.SplitCayleyLinearDerivation` (`L82`) | Wrapped `ZornMatrixCarrier` (zero global `IsScalarTower`/`SMulCommClass` on `ZornMatrix ℝ`), plus `LieActionLane` & `ZornVectorMatrix` transport | `g2ToBraidDerivationEquivCanonicalZorn`, `splitCayleyG2DerivationEquivCanonicalZorn`, `splitCayleyLinearDerivationEquivCanonicalZorn`, `canonicalZornDerivationsToIntDerivations`, `canonicalZornDerivationsEquivVectorDerivations`, `canonicalZornDerivationsEquivCarrier` (`≃ₗ⁅ℝ⁆`), `zornMatrixCarrierLieLane` | **Full `≃` / `≃ₗ⁅ℝ⁆`** via `ZornMatrixCarrier` / `ZornVectorMatrix ℝ`; **injective `→ₗ⁅ℤ⁆`** on raw `ZornMatrix ℝ`; `LieActionLane` on raw `ZornMatrix ℝ` & `DerivationLieLane ℝ EndCZ` |
| D32 | `RealSplitOctonionDerivation.SplitCayleyDerivation` (`Lie/RealSplitOctonionDerivation.lean:68`) | Raw `ZornMatrix ℝ` (additive-only `toAddHom`) | `splitCayleyDerivationEquivIntDerivations` | **Full `≃`** into `derivations ℤ (ZornMatrix ℝ)` |
| D33 | `G2H3ZornEntrywiseEmbedding.G2Derivation` / `entrywiseCompatibleG2` & `H3ZornF4Derivations` / `BaezF4H3Zorn.H3ZornJordanDerivation` (`L158, 218`) | Reuses existing `H3ZornJordanInstance` + unopened/local `IsScalarTower`/`SMulCommClass` | `h3ZornF4DerivationsEquivDerivations` (`≃ₗ⁅ℝ⁆`), `g2EntrywiseActionLane` (`LieActionLane`), `compatibleG2ToH3ZornDerivationLieHom` (injective `→ₗ⁅ℝ⁆`), `compatibleG2H3ZornDerivationLane`, `h3ZornF4DerivationLane` | **Full `≃ₗ⁅ℝ⁆`** for `H3ZornF4Derivations`; **`LieActionLane`** for general `G2Derivation`; **injective `→ₗ⁅ℝ⁆` + `DerivationLieLane`** for `entrywiseCompatibleG2` |
| D34 | `SplitOctonionDerivationAutomorphism.SplitOctonionDerivation` (`L80`) | Wrapped `SplitOctonionZornCarrier` (zero global diamond on `SplitOctonion`) + `LieActionLane` on `SplitOctonion` | `splitOctonionDerivationEquivDerivations`, `splitOctonionZornDerivationLieLane`, `splitOctonionZornActionLane`, `splitOctonionZornOnsagerSystem` | **Full `≃`** into `derivations ℝ SplitOctonionZornCarrier`; `LieActionLane ℝ SplitOctonion` on raw carrier |
| D35 | `NoncommutativeZornBdGDerivations.ZornDerivation A` (`L461`) | Wrapped `NCZornCarrier A` (`ℤ`-linear `ZornDerivation` vs `RealLinearNCZornDerivation`) | `ncZornDerivationEquivIntDerivations`, `ncZornDerivationLieLane`, `RealLinearNCZornDerivation` → `ncZornRealDerivationEquiv`, `ncZornRealDerivationLieLane` | **Full `≃`** into `derivations ℤ (NCZornCarrier A)` (and `derivations ℝ` for `RealLinearNCZornDerivation`) |
| D36 | `OperatorCoefficientZornExtension.OpDerivation H` (`L197`) | Wrapped `OpZornCarrier H` (`ℂ`-linear; local/wrapped `IsScalarTower`/`SMulCommClass`) | `opDerivationEquivComplexDerivations`, `opDerivationToRealDerivations` (`_injective`), `opDerivationToIntDerivations`, `opZornComplexDerivationLieLane`, `opZornRealDerivationLieLane` | **Full `≃`** into `derivations ℂ (OpZornCarrier H)`; **injective** scalar restriction into `derivations ℝ` & `derivations ℤ` |
| D37 | `AlbertDerivationsF4.JordanDerivation circ` (`Exceptional/AlbertDerivationsF4.lean:32`) | Wrapped `BilinearAlgRingCarrier P` / `BilinearAlgCarrier D` (`BilinearAlgData R J`) | `jordanDerivationEquivDerivations`, `bilinearAlgDerivationLieLane`, `bilinearAlgOnsagerSystem` | **Full `≃`** into `derivations R (BilinearAlgCarrier D)` (`[CommRing R]`, `R`-bilinear `circ`) |
| D38 | `PeirceGradedSuperderivations`: `IsSquareZeroRingDifferential` (`L27`) & odd superderivations (`oddDiff`, `differentialPlus`, `differentialMinus`, `differentialPhi`, `differentialJ` / `differentialJLinear`) | Ordinary ungraded Leibniz vs. `twist S`-odd super-Leibniz (`d(XY) = d(X)Y + twist S X * d(Y)`) | `squareZeroRingDifferentialToDerivations` (injective), `addLeibnizEquivIntDerivations` (`≃+`); `IsOddTwistSuperderivation`, `superAnticommToDerivations` & `superAnticommLinearToDerivations`, `superAnticommToDerivations_oddDiff_eq`, `superAnticommToDerivations_differentialPlus_differentialMinus_eq`, `oddSuperderivationEvenBimoduleHom`, `superAnticommLinearEvenRestrict`, `peirceEvenSubalgebraOnsagerSystem` | **Injective-only** for `IsSquareZeroRingDifferential`; **odd sectors are NOT ungraded Leibniz** — exact bridge is **super-anticommutator `{d₁, d₂}` closure** into `derivations ℤ/R B` + **even-subring/subalgebra restriction** + **bimodule** `even →+ odd` |
| D39 | `Canonical.BraidedDerivation` (`BraidedDerivation.lean:28`) & guarded `GradedBraidedDerivation` (`L3030`) | Upstream `HomogeneousElement` lacks grade membership (`⟨x, 0⟩` bypass); `GradedBraidedDerivation` enforces `a ∈ grade g` | `braidedDerivationToGraded` (injective), `gradedBraidedDerivation_isLeibniz_of_trivialDeg_of_span` / `_of_deg_zero_of_span`, `gradedBraidedDerivationToDerivations`, `gradedBraidedDerivationRestrictTrivialAdjoin`, `gradedBraidedDerivationLieLane`, `oddTwistSuperderivationToGradedBraided` (injective via `zmod2SignBicharacter` & `peirceZMod2Grade`) | **Conditional / Sector-Restricted:** Ungraded Leibniz holds ONLY when `IsLeibniz` holds (trivial braiding `IsTrivialBraidingDeg B D.deg` or `D.deg = 0` on a graded spanning set, or restricted to `gradedBraidedLeibnizSubalgebra`); `oddTwistSuperderivationToGradedBraided` embeds Peirce odd superderivations injectively into `GradedBraidedDerivation (ZMod 2)` |

*(Auxiliary spine combinators in `ModularDerivationLaneBridge` L1630–1816 and `ExceptionalZornSuperBraidedDerivationBridge` L57–115 supply `modularZDerivationLieLane`, `realDerivationLieLane`, `complexToRealDerivationLieLane`, `inducedActionLaneOnsagerSystem`, and `OnsagerFormPairing` evaluation lemmas.)*

---

## 3. Umbrella Capstone, Cross-Gap Theorems & Wiring

[`lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean`](../lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean) exports:
- **Core `Type`-level structures:** `UnifiedDerivationOnsagerFormSpine` (`ofParitySystem`, concrete `canonicalUnifiedDerivationOnsagerFormSpine`) and `LeibnizDerivationFrechetOnsagerSpine` (`canonicalStarCapstoneSpine`, `canonicalAutCapstoneSpine`, concrete `capstoneQubitSpine`), with zero `Prop`-only aggregate constructor structures.
- **All 6 cross-gap pair integration theorems:**
  - `gapAB_peirceCut_ceBKM_parity_bridge` & `gapAB_cartanSplit_parityFormPairing_bridge` (**Gap A + Gap B**),
  - `gapBC_frechetHessian_gibbsTrajectory_secondLaw` (**Gap B + Gap C**),
  - `gapAD_peirceCut_superAnticomm_cartan_bridge` & `gapAD_bridgedLane_cartanOnsager_bridge` (**Gap A + Gap D**),
  - `gapDB_modularDerivation_ceBKM_parityForm_bridge` & `gapDB_superBraided_ceBKM_curvature_bridge` (**Gap D + Gap B**),
  - `gapCD_modularDerivation_metriplecticFlow_secondLaw` & `gapCD_exceptionalSuperDerivation_metriplecticFlow_secondLaw` (**Gap C + Gap D**),
  - `gapAC_cartanSchur_metriplecticFlow_secondLaw` & `gapAC_peirceCut_matrixKuboMori_secondLaw` (**Gap A + Gap C**).
- **Master synthesis & concrete noncommutative witness:** `four_pillar_unified_capstone` and `capstone_qubit_nondegenerate_witness` (`n = 2`, proving `[switchOp2, tiltOp2] ≠ 0`, `0 < dissipative`, `0 < secondFDerivLogPartitionReadout.re`, `reversible ≠ 0`, `frechetExtDeriv = 0`, `onsager_casimir_master_reciprocity`, and `deriv_gibbsRelativePotential_metriplectic_neg_of_ne < 0`).
- **Umbrella Wiring:**
  - [`lean/InfoGeometry/Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean) imports M2, M3 (`BKMMetriplecticTrajectorySecondLaw` + `BKMMetriplecticTrajectorySecondLawGapCAudit`), M4A/M4B, and M5 Capstone + Audit, bringing all M1–M5 modules into the static default reachability closure of `InfoGeometry.All` / `InfoGeometry.AllExhaustive` (`audit_default_lean_sources.py`: 0 M1–M5 `missing_from_all`). Note that the `InfoGeometry.Canonical.All` Lake build target remains blocked solely on unrelated pre-existing upstream modules (`InfoGeometry.Canonical.MobiusKleinStatisticalZornPacket` and `InfoGeometry.Algebra.Zorn.G2FlagFactorizationRecursion`).
  - [`lean/InfoGeometry/Foundations/InfoGeometryCoreLibrary.lean`](../lean/InfoGeometry/Foundations/InfoGeometryCoreLibrary.lean) was left unmodified (and not built at `a7e91ecfcdb84f`) due to unrelated upstream `InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower` (actively modified in the working tree outside M1–M5 scope).

---

## 4. Serialized Validation Commands

All commands run serially from `/home/goutev/repos/info-geometry-lean` under the shared build lock `/tmp/info-geometry-build.lock` (never run bare `run_locked_lake_build.py` without explicit targets, and never run `lake clean`):

```bash
# 1. Single-file kernel elaboration with -DwarningAsError=true
python3 tools/infra/run_locked_lean.py --wait-for-build-lock \
  lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean -- -DwarningAsError=true
python3 tools/infra/run_locked_lean.py --wait-for-build-lock \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean -- -DwarningAsError=true
python3 tools/infra/run_locked_lean.py --wait-for-build-lock \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean -- -DwarningAsError=true

# 2. Explicit-target locked Lake build (omit --wfail so unrelated upstream warnings do not abort;
#    note InfoGeometry.Canonical.All and InfoGeometry.Foundations.InfoGeometryCoreLibrary remain
#    blocked on unrelated upstream modules outside M1-M5)
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge \
  InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridgeAudit \
  InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge \
  InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridgeAudit \
  InfoGeometry.SuperMetriplectic.All \
  InfoGeometry.Canonical.CEBKMParityUnificationBridge \
  InfoGeometry.Canonical.CEBKMParityUnificationBridgeAudit \
  InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw \
  InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLawGapCAudit \
  InfoGeometry.Canonical.ModularDerivationLaneBridge \
  InfoGeometry.Canonical.ModularDerivationLaneBridgeAudit \
  InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge \
  InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridgeAudit \
  InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone \
  InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstoneAudit

# 3. Lexical & compiled-.olean axiom verification
python3 tools/infra/axiom_audit.py --fail-on-gaps \
  lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean \
  lean/InfoGeometry/Canonical/All.lean
python3 tools/infra/axiom_index.py InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone
python3 tools/infra/axiom_check.py --batch-size 1 \
  InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge \
  InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridgeAudit \
  InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge \
  InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridgeAudit \
  InfoGeometry.SuperMetriplectic.All \
  InfoGeometry.Canonical.CEBKMParityUnificationBridgeAudit \
  InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw \
  InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLawGapCAudit \
  InfoGeometry.Canonical.ModularDerivationLaneBridge \
  InfoGeometry.Canonical.ModularDerivationLaneBridgeAudit \
  InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge \
  InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridgeAudit \
  InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone \
  InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstoneAudit
# (CEBKMParityUnificationBridge exceeds axiom_check.py's 300s batch timeout; check directly:)
flock -x /tmp/info-geometry-build.lock lake env lean --run tools/infra/axiom_check.lean \
  .lake/build/lib/lean/InfoGeometry/Canonical/CEBKMParityUnificationBridge.olean

# 4. Scoped quality, trap, reachability, and quarantine gates
python3 tools/quality/unified_gate.py \
  lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean \
  lean/InfoGeometry/Canonical/All.lean
python3 tools/infra/opengauss_screener.py --strict \
  lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean \
  lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean
python3 tools/quality/semantic_content_audit.py \
  --file-prefix lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawGapCAudit.lean \
  --file-prefix lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstone.lean \
  --file-prefix lean/InfoGeometry/Canonical/LeibnizDerivationFrechetOnsagerCapstoneAudit.lean \
  --gate
python3 tools/infra/audit_default_lean_sources.py
bash scripts/enforce_quarantine_imports.sh
```
