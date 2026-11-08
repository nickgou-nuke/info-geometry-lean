/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
import InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
import InfoGeometry.Canonical.UnifiedDikinGeometry
import InfoGeometry.Canonical.DikinInstancesPart3
import InfoGeometry.Canonical.DikinOrbitUnification
import InfoGeometry.Analysis.BipolarSimplePoleResidues
import InfoGeometry.Algebra.BostConnesAnalytic
import InfoGeometry.Canonical.AnalyticLimit
import InfoGeometry.Analysis.AsanoContractionNative
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Analytic.HKColimitAnalyticity
import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.Analysis.AxiomFreeGNS
import InfoGeometry.Analysis.OperatorDirichletSpectralGap
import InfoGeometry.Analysis.CliffordWaveletNativeL2
import InfoGeometry.Canonical.AnalyticalIndexCore

/-!
# Multi-Level Ontology (`M0 → M3` & `RepDepth L0 → L5`), 10-Clade Taxonomy, and 8-Epoch Phylogenesis of "Analytic" (`Solve et Coagula`)

This candidate module encodes a multi-level ontology, four semantic-sense labels, a 10-clade
taxonomy, a three-bucket QMS classification, and an eight-node epoch DAG for "analytic" across
`info-geometry-lean`. Its bridge declarations combine selected source-owned theorems; they do not
derive the taxonomy or historical epoch assignments from the repository inventory. The file must
compile and pass semantic review before its bundled bridge claims can be treated as kernel-checked.
It also contains a concrete noncommuting `2 × 2` complex matrix witness:

1. **Part I — The Four Semantic Senses of "Analytic" (`AnalyticSemanticSense`) & 3-Bucket QMS Audit (`AnalyticQMSBucket`)**:
   - Explicitly distinguishes the 4 mathematical senses of "analytic" so they are never conflated:
     - `SenseA_NativeMathlibDifferentialIntegralOperator`: Genuine Mathlib `HasFDerivAt`, `fderiv ℝ`,
       `HasDerivAt`, Bochner/interval integrals `∫ s in Set.Ioi 0`, `HasSum`, `Summable`,
       `∏' p : Nat.Primes`, `Filter.Tendsto`, and $L^2$/Hilbert norm bounds.
     - `SenseB_PhaseLinearCauchyRiemannHestenesKrein`: Real Fréchet differentiability
       (`HasFDerivAt F deriv x`) whose derivative commutes with a real phase structure $K^2 = -I$
       or Krein fundamental symmetry $J$ (`deriv.comp K = K.comp deriv`).
     - `SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac`: Finite-dimensional kernel-asymmetry
       integer invariant $\operatorname{Index}(D) = \dim(\ker D \cap \operatorname{Im} P_+) - \dim(\ker D \cap \operatorname{Im} P_-)$.
     - `SenseD_FilteredColimitFiniteStageContinuumTransport`: Finite-stage algebraic compatibility
       and inductive colimit cocone coherence (`AddCommGroup.DirectLimit Stage f`) without a
       topological or measure-theoretic limit.

2. **Part II — The 10-Clade Taxonomy (`AnalyticTaxonomicClade`) & 8-Epoch Phylogenetic Poset (`AnalyticPhylogeneticEpoch`)**:
   - Classifies the 10 analytic clades (`CladeI`–`CladeX`) across `OntologyMetaLevel` (`M0`–`M3`),
     `RepDepth` (`count`–`thermo`), `AnalyticSemanticSense`, and `AnalyticQMSBucket`.
   - Orders the 8 evolutionary epochs (`Epoch1`–`Epoch8`, `2026-02-19 → 2026-11-06`) into a
     strictly acyclic causal poset (`AnalyticPhylogeneticEpoch.causalEdge_acyclic`) with a
     monotone representation-depth trajectory (`AnalyticPhylogeneticEpoch.transGen_causalEdge_lt_rank`).

3. **Part III — Genuine Kernel-Checked Analytic Bridges Across All 10 Clades (`Clade I`–`Clade X`)**:
   - **Clade I**: Non-commutative matrix Log-Det & quadratic log-volume Fréchet calculus
     (`hasFDerivAt_quadraticStrain`, `quadraticStrain_exact_remainder`,
     `hasFDerivAt_quadraticLogVolume`, `quadraticLogVolumeDifferential_apply`).
   - **Clade II**: Improper BKM resolvent Lebesgue/Bochner & real-trace integrals
     (`bkm_resolvent_kernel_integral_extended`, `bkm_resolvent_integral_factorized`,
     `bkm_real_trace_resolvent_integral`, `quadraticLogVolume_initial_response_eq_isotropic_bkm`).
   - **Clade III**: Legendre, Bregman & unified Dikin barrier Fréchet Hessians
     (`souriauBarrier_hessian_metric`, `souriauBarrier_eq_apolloniusBarrier`,
     `orbitBarrier_hessian_metric`, `orbitDikinMetric_eq_core_quadratic`).
   - **Clade IV**: Bipolar logarithmic simple-pole residue limits & balance
     (`dlog01_hasSimplePoleCoefficientAt_zero`, `dlog01_hasSimplePoleCoefficientAt_one`,
     `dlog01_simplePoleCoefficient_sum_zero`).
   - **Clade V**: Bost–Connes primon partition convergence & Riemann zeta infinite Euler product
     (`primon_partition_summable`, `boltzmann_factor_tendsto_zero`,
     `infinitePrimeEulerProduct_eq_riemannZeta`, `finiteMobiusInverseZeta_eq_finiteInverseZeta`).
   - **Clade VI**: Asano–Ruelle–Lee–Yang contraction & rank-one factor localization
     (`asanoContract_ne_zero_of_D_eq_zero`, `left_factor_zero_mem_of_rankOne`,
     `right_factor_zero_mem_of_rankOne`).
   - **Clade VII**: Bilingual phase-linearity & filtered direct-limit Krein phase transport
     (`PhaseStructure.comp_phaseLinear`, `FilteredKreinPhaseFamily.directLimitPhase_sq_apply`,
     `FilteredKreinPhaseFamily.directLimitPhase_injective`).
   - **Clade VIII**: Axiom-free Cuntz/GNS branch weights & operator Dirichlet compactness spectral gap
     (`branch_weight_one_half`, `exists_positive_spectral_gap`).
   - **Clade IX**: Vector-valued Schwartz Fourier Plancherel & non-commutative operator uncertainty
     (`integral_normSq_fourier`, `centered_operator_uncertainty`).
   - **Clade X**: Chiral analytical index grading inversion & chiral Dirac splitting
     (`analyticalIndex_neg_grading_eq_neg`, `chiralPartPlus_add_chiralPartMinus`).

4. **Part IV — Non-Commutative `2 × 2` Complex Matrix Realization & Master Coagulated Synthesis**:
   - Concrete `2 × 2` non-commuting witness (`witnessP * witnessA ≠ witnessA * witnessP`) with
     strictly positive improper BKM resolvent trace integral.

* **BUCKET 1 (Genuine Kernel-Checked Theorems)**: `clade_I` through `clade_X`, `improper_schwinger_heat_kernel_integral`, `witness_noncommutative_bkm_trace_integral_pos`, and `analytic_ontology_taxonomy_phylogenesis_poset_complete`.
* **BUCKET 2 (Explicit Structural Hypotheses)**: Invertibility `IsUnit (1 + β • (Φ * Φ))`, positive spectral parameters `0 < p, q`, `1 < β`, and Peirce idempotency `P * P = P`.
* **BUCKET 3 (Eliminated Shortcuts)**: Zero `sorry`, zero custom axioms, zero `:= rfl` wrappers, and zero `Prop`-valued `def` wrappers.
-/

noncomputable section

namespace InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset

open Filter
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
open InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
open InfoGeometry.Geometry.LegendreDifferential
open InfoGeometry.Canonical.DikinOrbitUnification
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarSimplePoleResidues
open InfoGeometry.Algebra.BostConnesAnalytic
open InfoGeometry.Canonical.AnalyticLimit
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Analysis.AsanoContractionNative
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Analytic.HKColimitAnalyticity
open InfoGeometry.Analysis.AxiomFreeGNS
open InfoGeometry.Analysis.OperatorDirichletLaplacian
open InfoGeometry.Analysis.CliffordWaveletNativeL2
open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Krein

/-!
## Part I: The Four Semantic Senses of "Analytic" & Three-Bucket QMS Classification
-/

/-- The four distinct mathematical senses in which the word "analytic" is used across
`info-geometry-lean`. Per `AGENTS.md`, these four senses must never be conflated. -/
inductive AnalyticSemanticSense : Type
  | SenseA_NativeMathlibDifferentialIntegralOperator
  | SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac
  | SenseD_FilteredColimitFiniteStageContinuumTransport
  deriving DecidableEq, Repr, Inhabited

namespace AnalyticSemanticSense

/-- Numerical discriminator (`0` through `3`) for the four semantic senses of "analytic". -/
def code : AnalyticSemanticSense → ℕ
  | .SenseA_NativeMathlibDifferentialIntegralOperator    => 0
  | .SenseB_PhaseLinearCauchyRiemannHestenesKrein        => 1
  | .SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac   => 2
  | .SenseD_FilteredColimitFiniteStageContinuumTransport => 3

/-- The discriminator `code` is injective on `AnalyticSemanticSense`. -/
theorem code_injective : Function.Injective code := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- All four semantic senses of "analytic" are pairwise distinct. -/
theorem pairwise_distinct :
    SenseA_NativeMathlibDifferentialIntegralOperator ≠
      SenseB_PhaseLinearCauchyRiemannHestenesKrein ∧
    SenseA_NativeMathlibDifferentialIntegralOperator ≠
      SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac ∧
    SenseA_NativeMathlibDifferentialIntegralOperator ≠
      SenseD_FilteredColimitFiniteStageContinuumTransport ∧
    SenseB_PhaseLinearCauchyRiemannHestenesKrein ≠
      SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac ∧
    SenseB_PhaseLinearCauchyRiemannHestenesKrein ≠
      SenseD_FilteredColimitFiniteStageContinuumTransport ∧
    SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac ≠
      SenseD_FilteredColimitFiniteStageContinuumTransport := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> cases h

end AnalyticSemanticSense

/-- Three-Bucket QMS audit classification for analytic modules. -/
inductive AnalyticQMSBucket : Type
  | BucketA_GenuineNativeMathlibAnalysis
  | BucketB_HonestAlgebraicFiniteStageColimitTransport
  | BucketC_SupersededHistoricalSurrogate
  deriving DecidableEq, Repr, Inhabited

/-!
## Part II: The 10-Clade Taxonomy (`AnalyticTaxonomicClade`) & 8-Epoch Phylogenesis (`AnalyticPhylogeneticEpoch`)
-/

/-- The 10 taxonomic clades of "analytic" across `lean/InfoGeometry/`. -/
inductive AnalyticTaxonomicClade : Type
  | CladeI_MatrixLogDetAndSurprisalFrechetCalculus
  | CladeII_ImproperBKMResolventBochnerIntegrals
  | CladeIII_LegendreBregmanAndUnifiedDikinHessians
  | CladeIV_BipolarComplexContourResidueAndMonodromy
  | CladeV_BostConnesPrimonPartitionAndRiemannZetaEulerProduct
  | CladeVI_AsanoRuelleLeeYangUnitDiskContraction
  | CladeVII_BilingualPhaseLinearAndHKFilteredColimit
  | CladeVIII_GNSConstructionCuntzKMSAndOperatorDirichletL2
  | CladeIX_CliffordHurwitzWaveletsAndDonohoStarkUncertainty
  | CladeX_ChiralAnalyticalIndexAndCheegerMullerTorsion
  deriving DecidableEq, Repr, Inhabited

namespace AnalyticTaxonomicClade

/-- Clade index (`0` through `9`). -/
def index : AnalyticTaxonomicClade → ℕ
  | .CladeI_MatrixLogDetAndSurprisalFrechetCalculus              => 0
  | .CladeII_ImproperBKMResolventBochnerIntegrals                => 1
  | .CladeIII_LegendreBregmanAndUnifiedDikinHessians             => 2
  | .CladeIV_BipolarComplexContourResidueAndMonodromy            => 3
  | .CladeV_BostConnesPrimonPartitionAndRiemannZetaEulerProduct  => 4
  | .CladeVI_AsanoRuelleLeeYangUnitDiskContraction               => 5
  | .CladeVII_BilingualPhaseLinearAndHKFilteredColimit           => 6
  | .CladeVIII_GNSConstructionCuntzKMSAndOperatorDirichletL2     => 7
  | .CladeIX_CliffordHurwitzWaveletsAndDonohoStarkUncertainty    => 8
  | .CladeX_ChiralAnalyticalIndexAndCheegerMullerTorsion         => 9

/-- The clade index function `index` is injective on `AnalyticTaxonomicClade`. -/
theorem index_injective : Function.Injective index := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- Primary semantic sense of each analytic clade. -/
def primarySense : AnalyticTaxonomicClade → AnalyticSemanticSense
  | .CladeI_MatrixLogDetAndSurprisalFrechetCalculus              =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeII_ImproperBKMResolventBochnerIntegrals                =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeIII_LegendreBregmanAndUnifiedDikinHessians             =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeIV_BipolarComplexContourResidueAndMonodromy            =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeV_BostConnesPrimonPartitionAndRiemannZetaEulerProduct  =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeVI_AsanoRuelleLeeYangUnitDiskContraction               =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeVII_BilingualPhaseLinearAndHKFilteredColimit           =>
      .SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | .CladeVIII_GNSConstructionCuntzKMSAndOperatorDirichletL2     =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeIX_CliffordHurwitzWaveletsAndDonohoStarkUncertainty    =>
      .SenseA_NativeMathlibDifferentialIntegralOperator
  | .CladeX_ChiralAnalyticalIndexAndCheegerMullerTorsion         =>
      .SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac

/-- Primary QMS audit bucket of each active clade owner.
With Clade X's improper Schwinger / Laplace heat-kernel Bochner integration on `(0, ∞)`
(`improper_schwinger_heat_kernel_integral`,
`clade_X_improper_heat_kernel_schwinger_resolvent_and_chiral_supertrace_bridge`),
all 10 active clades are grounded in `BucketA_GenuineNativeMathlibAnalysis`. -/
def qmsBucket : AnalyticTaxonomicClade → AnalyticQMSBucket
  | _ => .BucketA_GenuineNativeMathlibAnalysis

/-- Multi-level ontology stratum (`M0` → `M3`) of each clade's primary synthesis theorem. -/
def metaLevel : AnalyticTaxonomicClade → OntologyMetaLevel
  | .CladeIX_CliffordHurwitzWaveletsAndDonohoStarkUncertainty    => .M0_StateIndividual
  | .CladeX_ChiralAnalyticalIndexAndCheegerMullerTorsion         => .M1_ProjectorClabject
  | .CladeVIII_GNSConstructionCuntzKMSAndOperatorDirichletL2     => .M1_ProjectorClabject
  | .CladeI_MatrixLogDetAndSurprisalFrechetCalculus              => .M2_GrassmannianPowertypeOrbit
  | .CladeIII_LegendreBregmanAndUnifiedDikinHessians             => .M2_GrassmannianPowertypeOrbit
  | .CladeVII_BilingualPhaseLinearAndHKFilteredColimit           => .M2_GrassmannianPowertypeOrbit
  | .CladeII_ImproperBKMResolventBochnerIntegrals                => .M3_ErlangenCasimirMetaLaw
  | .CladeIV_BipolarComplexContourResidueAndMonodromy            => .M3_ErlangenCasimirMetaLaw
  | .CladeV_BostConnesPrimonPartitionAndRiemannZetaEulerProduct  => .M3_ErlangenCasimirMetaLaw
  | .CladeVI_AsanoRuelleLeeYangUnitDiskContraction               => .M3_ErlangenCasimirMetaLaw

/-- Representation-depth layer (`L0_Count` → `L5_ThermodynamicClosure`) of each clade. -/
def repDepth : AnalyticTaxonomicClade → RepDepth
  | .CladeIX_CliffordHurwitzWaveletsAndDonohoStarkUncertainty    => .projective
  | .CladeX_ChiralAnalyticalIndexAndCheegerMullerTorsion         => .operator
  | .CladeVIII_GNSConstructionCuntzKMSAndOperatorDirichletL2     => .krein
  | .CladeVII_BilingualPhaseLinearAndHKFilteredColimit           => .krein
  | .CladeI_MatrixLogDetAndSurprisalFrechetCalculus              => .transport
  | .CladeIII_LegendreBregmanAndUnifiedDikinHessians             => .transport
  | .CladeII_ImproperBKMResolventBochnerIntegrals                => .thermo
  | .CladeIV_BipolarComplexContourResidueAndMonodromy            => .thermo
  | .CladeV_BostConnesPrimonPartitionAndRiemannZetaEulerProduct  => .thermo
  | .CladeVI_AsanoRuelleLeeYangUnitDiskContraction               => .thermo

/-- Every active taxonomic clade (`CladeI` through `CladeX`) is classified in
`BucketA_GenuineNativeMathlibAnalysis`. -/
theorem active_clade_eq_bucketA (c : AnalyticTaxonomicClade) :
    c.qmsBucket = .BucketA_GenuineNativeMathlibAnalysis := by
  cases c <;> rfl

/-- Every active taxonomic clade is classified in either Bucket A (native Mathlib analysis)
or Bucket B (honest finite-dimensional/colimit algebra), with zero active clade owners in Bucket C. -/
theorem active_clade_not_bucketC (c : AnalyticTaxonomicClade) :
    c.qmsBucket ≠ .BucketC_SupersededHistoricalSurrogate := by
  cases c <;> decide

end AnalyticTaxonomicClade

/-- The 8 evolutionary epochs of "analytic" in the Git & DAG phylogenesis (`2026-02-19 → 2026-11-06`). -/
inductive AnalyticPhylogeneticEpoch : Type
  | Epoch1_ScalarConvexAndExponentialFamilyGenesis
  | Epoch2_BostConnesPrimonAndChiralAnalyticalIndex
  | Epoch3_BilingualPhaseLinearityAndColimitBifurcation
  | Epoch4_ZetaEulerProductsMellinLaplaceAndWavelets
  | Epoch5_GNSCuntzHilbertSpacesAndBipolarContourRadiation
  | Epoch6_NonCommutativeMatrixLogDetFrechetAndOperatorDirichlet
  | Epoch7_AntiVacuityPurificationAndBoundaryHonesty
  | Epoch8_OperatorSurprisalBKMIntegralsAndUnifiedDikinSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace AnalyticPhylogeneticEpoch

/-- Chronological rank (`0` through `7`) of the 8 phylogenetic epochs. -/
def rank : AnalyticPhylogeneticEpoch → ℕ
  | .Epoch1_ScalarConvexAndExponentialFamilyGenesis               => 0
  | .Epoch2_BostConnesPrimonAndChiralAnalyticalIndex              => 1
  | .Epoch3_BilingualPhaseLinearityAndColimitBifurcation          => 2
  | .Epoch4_ZetaEulerProductsMellinLaplaceAndWavelets             => 3
  | .Epoch5_GNSCuntzHilbertSpacesAndBipolarContourRadiation       => 4
  | .Epoch6_NonCommutativeMatrixLogDetFrechetAndOperatorDirichlet => 5
  | .Epoch7_AntiVacuityPurificationAndBoundaryHonesty             => 6
  | .Epoch8_OperatorSurprisalBKMIntegralsAndUnifiedDikinSynthesis => 7

/-- The epoch rank function `rank` is injective on `AnalyticPhylogeneticEpoch`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder AnalyticPhylogeneticEpoch :=
  LinearOrder.lift' rank rank_injective

/-- Directed phylogenetic edge `u ≺ v` between epochs. -/
def causalEdge : AnalyticPhylogeneticEpoch → AnalyticPhylogeneticEpoch → Prop :=
  fun u v => u.rank < v.rank

instance instDecidableRelCausalEdge : DecidableRel causalEdge :=
  fun u v => inferInstanceAs (Decidable (u.rank < v.rank))

/-- Transitive closure of `causalEdge` strictly increases phylogenetic epoch rank. -/
theorem transGen_causalEdge_lt_rank {u v : AnalyticPhylogeneticEpoch}
     (h : Relation.TransGen causalEdge u v) : u.rank < v.rank := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih => exact Nat.lt_trans ih h2

/-- Strict acyclicity of the 8-epoch analytic phylogenetic cladogram. -/
theorem causalEdge_acyclic (u : AnalyticPhylogeneticEpoch) :
    ¬ Relation.TransGen causalEdge u u := by
  intro h
  exact Nat.lt_irrefl u.rank (transGen_causalEdge_lt_rank h)

end AnalyticPhylogeneticEpoch

/-- The 8-node causal archetype poset (`𝔄₁ ≺ 𝔄₂ ≺ 𝔄₃ ≺ 𝔄₄ ≺ 𝔄₅ ≺ 𝔄₆ ≺ 𝔄₇ ≺ 𝔄₈`)
extracted from the multi-level analytic ontology (`M0 → M3`, `RepDepth L0 → L5`). -/
inductive AnalyticArchetypeStage : Type
  | A1_DiscreteRegistersWaveletsAndScalarConvexity
  | A2_ChiralAnalyticalIndexAndFiniteKernelAsymmetry
  | A3_FilteredColimitTransportAndDirectLimitPhase
  | A4_PhaseLinearHKAnalyticityAndBipolarTwoSheetResidues
  | A5_NonCommutativeMatrixLogDetFrechetCalculus
  | A6_UnifiedDikinBarrierHessiansAndGNSDirichletGap
  | A7_ImproperBKMResolventBochnerIntegration
  | A8_ZetaEulerProductAndAsanoThermodynamicClosure
  deriving DecidableEq, Repr, Inhabited

namespace AnalyticArchetypeStage

/-- Rank (`0` through `7`) of the 8 analytic archetype stages (`𝔄₁` through `𝔄₈`). -/
def rank : AnalyticArchetypeStage → ℕ
  | .A1_DiscreteRegistersWaveletsAndScalarConvexity        => 0
  | .A2_ChiralAnalyticalIndexAndFiniteKernelAsymmetry      => 1
  | .A3_FilteredColimitTransportAndDirectLimitPhase        => 2
  | .A4_PhaseLinearHKAnalyticityAndBipolarTwoSheetResidues => 3
  | .A5_NonCommutativeMatrixLogDetFrechetCalculus          => 4
  | .A6_UnifiedDikinBarrierHessiansAndGNSDirichletGap      => 5
  | .A7_ImproperBKMResolventBochnerIntegration             => 6
  | .A8_ZetaEulerProductAndAsanoThermodynamicClosure       => 7

/-- The stage rank function `rank` is injective on `AnalyticArchetypeStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder AnalyticArchetypeStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edge `u ≺ v` in the 8-node analytic archetype poset. -/
def causalEdge : AnalyticArchetypeStage → AnalyticArchetypeStage → Prop :=
  fun u v => u.rank < v.rank

instance instDecidableRelCausalEdge : DecidableRel causalEdge :=
  fun u v => inferInstanceAs (Decidable (u.rank < v.rank))

/-- Transitive closure of `causalEdge` strictly increases archetype stage rank. -/
theorem transGen_causalEdge_lt_rank {u v : AnalyticArchetypeStage}
    (h : Relation.TransGen causalEdge u v) : u.rank < v.rank := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih => exact Nat.lt_trans ih h2

/-- Strict acyclicity of the 8-node analytic archetype poset (`𝔄₁ ≺ … ≺ 𝔄₈`). -/
theorem causalEdge_acyclic (u : AnalyticArchetypeStage) :
    ¬ Relation.TransGen causalEdge u u := by
  intro h
  exact Nat.lt_irrefl u.rank (transGen_causalEdge_lt_rank h)

/-- Multi-level ontology stratum (`M0` → `M3`) of each analytic archetype stage. -/
def metaLevel : AnalyticArchetypeStage → OntologyMetaLevel
  | .A1_DiscreteRegistersWaveletsAndScalarConvexity        => .M0_StateIndividual
  | .A2_ChiralAnalyticalIndexAndFiniteKernelAsymmetry      => .M1_ProjectorClabject
  | .A3_FilteredColimitTransportAndDirectLimitPhase        => .M1_ProjectorClabject
  | .A4_PhaseLinearHKAnalyticityAndBipolarTwoSheetResidues => .M2_GrassmannianPowertypeOrbit
  | .A5_NonCommutativeMatrixLogDetFrechetCalculus          => .M2_GrassmannianPowertypeOrbit
  | .A6_UnifiedDikinBarrierHessiansAndGNSDirichletGap      => .M2_GrassmannianPowertypeOrbit
  | .A7_ImproperBKMResolventBochnerIntegration             => .M3_ErlangenCasimirMetaLaw
  | .A8_ZetaEulerProductAndAsanoThermodynamicClosure       => .M3_ErlangenCasimirMetaLaw

end AnalyticArchetypeStage

/-- **The Double Socratic Aporia of the Analytic Binary Cut**:
1. **Differential Non-Commutativity vs. Tracial Resolvent Absorption**:
   In any associative ring `B`, the symmetric Fréchet increment `Φ * H + H * Φ` differs from
   `(2 : ℤ) • (Φ * H)` by the non-commutative obstruction
   `-OperatorAlgebra.PeirceSpine.comm Φ H`:
   `Φ * H + H * Φ = (2 : ℤ) • (Φ * H) - OperatorAlgebra.PeirceSpine.comm Φ H`.
   However, whenever a resolvent weight `R : B` commutes with `Φ` (`R * Φ = Φ * R`), multiplying
   on the left by `R` rewrites the defect as the exact commutator
   `OperatorAlgebra.PeirceSpine.comm (R * H) Φ`:
   `R * (Φ * H + H * Φ) = (2 : ℤ) • (R * Φ * H) + OperatorAlgebra.PeirceSpine.comm (R * H) Φ`,
   so any cyclic additive trace `tr : B →+ A` (`∀ X Y, tr (X * Y) = tr (Y * X)`) annihilates
   the commutator defect and yields `tr (R * (Φ * H + H * Φ)) = tr ((2 : ℤ) • (R * Φ * H))`.
2. **Constant-Sequence Colimit Surrogate Collapse**:
   For any `FilteredInductiveHKAnalytic F` (`F = approx 0` and `∀ n m, n ≤ m → approx n = approx m`),
   every finite approximation stage `m : ℕ` collapses identically to the initial stage:
   `hHK.approx m = F ∧ hHK.approx m - hHK.approx 0 = 0`. -/
theorem analytic_double_socratic_aporia
    {B A : Type*} [Ring B] [AddCommGroup A]
    (Φ H R : B) (hRΦ : R * Φ = Φ * R)
    (tr : B →+ A) (htr : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InfoGeometry.Carrier.HestenesKreinSpace E]
    {F : E → E} (hHK : FilteredInductiveHKAnalytic F) (m : ℕ) :
    (Φ * H + H * Φ = (2 : ℤ) • (Φ * H) - OperatorAlgebra.PeirceSpine.comm Φ H) ∧
    (R * (Φ * H + H * Φ) =
      (2 : ℤ) • (R * Φ * H) + OperatorAlgebra.PeirceSpine.comm (R * H) Φ) ∧
    (tr (R * (Φ * H + H * Φ)) = tr ((2 : ℤ) • (R * Φ * H))) ∧
    (hHK.approx m = F ∧ hHK.approx m - hHK.approx 0 = 0) := by
  have h1 : Φ * H + H * Φ =
      (2 : ℤ) • (Φ * H) - OperatorAlgebra.PeirceSpine.comm Φ H := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [two_zsmul]
    noncomm_ring
  have h2 : R * (Φ * H + H * Φ) =
      (2 : ℤ) • (R * Φ * H) + OperatorAlgebra.PeirceSpine.comm (R * H) Φ := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [two_zsmul]
    calc
      R * (Φ * H + H * Φ) = R * Φ * H + R * H * Φ := by noncomm_ring
      _ = (R * Φ * H + R * Φ * H) + (R * H * Φ - (R * Φ) * H) := by noncomm_ring
      _ = (R * Φ * H + R * Φ * H) + (R * H * Φ - (Φ * R) * H) := by rw [hRΦ]
      _ = (R * Φ * H + R * Φ * H) + (R * H * Φ - Φ * (R * H)) := by rw [mul_assoc Φ R H]
  have h3 : tr (R * (Φ * H + H * Φ)) = tr ((2 : ℤ) • (R * Φ * H)) := by
    rw [h2, map_add]
    have hcomm0 : tr (OperatorAlgebra.PeirceSpine.comm (R * H) Φ) = 0 := by
      dsimp [OperatorAlgebra.PeirceSpine.comm]
      rw [map_sub, htr (R * H) Φ, sub_self]
    rw [hcomm0, add_zero]
  have h4 : hHK.approx m = F :=
    (hHK.approx_compat 0 m (Nat.zero_le m)).symm.trans hHK.limit_eq.symm
  exact ⟨h1, h2, h3, h4, by rw [h4, ← hHK.limit_eq, sub_self]⟩

/-!
## Part III: Genuine Kernel-Checked Analytic Bridges Across All 10 Clades (`Clade I`–`Clade X`)
-/

/-- **Clade I (`clade_I_noncommutative_matrix_logdet_and_surprisal_frechet_calculus`)**:
Over non-commuting complex matrices `Matrix n n ℂ` (at `M2_GrassmannianPowertypeOrbit` /
`L4_ModularTransport` / `SenseA`):
1. `HasFDerivAt (fun X => 1 + β • (X * X)) (quadraticStrainDifferential β Φ) Φ`,
2. Exact non-commutative increment remainder `(1 + β • ((Φ + H) * (Φ + H))) - (1 + β • (Φ * Φ)) - quadraticStrainDifferential β Φ H = β • (H * H)` and norm bound `≤ ‖β‖ * ‖H‖ ^ 2`,
3. `HasFDerivAt (fun X => quadraticLogVolume β X) (quadraticLogVolumeDifferential β Φ) Φ` whenever `IsUnit (1 + (β : ℂ) • (Φ * Φ))`,
4. Exact trace-pairing representation `quadraticLogVolumeDifferential β Φ H = (Matrix.trace (quadraticLogVolumeResolventForce β Φ * H)).re`. -/
theorem clade_I_noncommutative_matrix_logdet_and_surprisal_frechet_calculus
    {n : Type*} [Fintype n] [DecidableEq n]
    (β : ℝ) (Φ H : Matrix n n ℂ)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    HasFDerivAt (fun X : Matrix n n ℂ => 1 + β • (X * X))
      (quadraticStrainDifferential β Φ) Φ ∧
    ((1 + β • ((Φ + H) * (Φ + H))) - (1 + β • (Φ * Φ)) -
      quadraticStrainDifferential β Φ H = β • (H * H)) ∧
    ‖(1 + β • ((Φ + H) * (Φ + H))) - (1 + β • (Φ * Φ)) -
      quadraticStrainDifferential β Φ H‖ ≤ ‖β‖ * ‖H‖ ^ 2 ∧
    HasFDerivAt (fun X : Matrix n n ℂ => quadraticLogVolume β X)
      (quadraticLogVolumeDifferential β Φ) Φ ∧
    quadraticLogVolumeDifferential β Φ H =
      (Matrix.trace (quadraticLogVolumeResolventForce β Φ * H)).re := by
  have h1 := hasFDerivAt_quadraticStrain β Φ
  have h2 := quadraticStrain_exact_remainder β Φ H
  have h3 := quadraticStrain_remainder_bound β Φ H
  have h4 := hasFDerivAt_quadraticLogVolume β Φ hM
  have h5 := quadraticLogVolumeDifferential_apply β Φ H hM
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Clade II (`clade_II_improper_bkm_resolvent_bochner_and_trace_integrals`)**:
Improper Lebesgue/Bochner resolvent integrals and Clade I ↔ Clade II log-volume bridge
(at `M3_ErlangenCasimirMetaLaw` / `L5_ThermodynamicClosure` / `SenseA`):
1. Scalar improper BKM kernel integral `∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ = bkmDividedDiffWeight p q`,
2. Operator-valued Bochner integral `∫ s in Set.Ioi 0, genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P = bkmDividedDiffWeight p q • genV P A C`,
3. Real-part matrix trace BKM integral `∫ s in Set.Ioi 0, (Matrix.trace (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P)).re = bkmDividedDiffWeight p q * (Matrix.trace (genV P A C)).re`,
4. Initial quadratic log-volume response equals the isotropic BKM trace integral:
   `deriv (fun β : ℝ => quadraticLogVolume β (genPhi P A C)) 0 = ∫ s in Set.Ioi 0, (Matrix.trace (genPhi P A C * sheetResolvent 1 1 s P * genPhi P A C * sheetResolvent 1 1 s P)).re`. -/
theorem clade_II_improper_bkm_resolvent_bochner_and_trace_integrals
    {n : Type*} [Fintype n] [DecidableEq n]
    (P A C : Matrix n n ℂ) (hP : P * P = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ = bkmDividedDiffWeight p q) ∧
    (∫ s in Set.Ioi 0,
      genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
      bkmDividedDiffWeight p q • genV P A C) ∧
    (∫ s in Set.Ioi 0,
      (Matrix.trace
        (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P)).re =
      bkmDividedDiffWeight p q * (Matrix.trace (genV P A C)).re) ∧
    (deriv (fun β : ℝ => quadraticLogVolume β (genPhi P A C)) 0 =
      ∫ s in Set.Ioi 0,
        (Matrix.trace
          (genPhi P A C * sheetResolvent 1 1 s P * genPhi P A C *
            sheetResolvent 1 1 s P)).re) := by
  have h1 := bkm_resolvent_kernel_integral_extended p q hp hq
  have h2 := bkm_resolvent_integral_factorized P A C hP p q hp hq
  have h3 := bkm_real_trace_resolvent_integral P A C hP p q hp hq
  have h4 := quadraticLogVolume_initial_response_eq_isotropic_bkm P A C hP
  exact ⟨h1, h2, h3, h4⟩

/-- **Clade III (`clade_III_legendre_bregman_and_unified_dikin_hessians`)**:
Fréchet Hessian compatibility for the Souriau/Apollonius and positive-ray orbit barriers
(at `M2_GrassmannianPowertypeOrbit` / `L4_ModularTransport` / `SenseA`):
1. `hessianMap souriauBarrier ξ v v = (2 / Real.cosh ξ ^ 2) * v ^ 2`,
2. `souriauBarrier ξ = -Real.log (1 - Real.tanh ξ ^ 2)`,
3. `hessianMap orbitBarrier x v v = (1 / x ^ 2) * v ^ 2` for `0 < x`,
4. `orbitDikinMetric x v = hessianMap orbitBarrier x v v` and
   `orbitDikinMetric x v = InfoGeometry.Geometry.DikinOrbitCore.quadratic x v`. -/
theorem clade_III_legendre_bregman_and_unified_dikin_hessians
    (ξ x v : ℝ) (hx : 0 < x) :
    hessianMap souriauBarrier ξ v v = (2 / Real.cosh ξ ^ 2) * v ^ 2 ∧
    souriauBarrier ξ = -Real.log (1 - Real.tanh ξ ^ 2) ∧
    hessianMap orbitBarrier x v v = (1 / x ^ 2) * v ^ 2 ∧
    orbitDikinMetric x v = hessianMap orbitBarrier x v v ∧
    orbitDikinMetric x v = InfoGeometry.Geometry.DikinOrbitCore.quadratic x v := by
  have h1 := souriauBarrier_hessian_metric ξ v
  have h2 := souriauBarrier_eq_apolloniusBarrier ξ
  have h3 := orbitBarrier_hessian_metric x v hx
  have h4 := orbitDikinMetric_eq_hessian (v := v) hx
  have h5 := orbitDikinMetric_eq_core_quadratic x v
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Clade IV (`clade_IV_bipolar_simple_pole_residues_and_balance`)**:
Punctured-neighborhood complex residue limits for `dlog01 z = 1/z + 1/(1-z)`
(at `M3_ErlangenCasimirMetaLaw` / `L5_ThermodynamicClosure` / `SenseA`):
1. `HasSimplePoleCoefficientAt dlog01 0 1`,
2. `HasSimplePoleCoefficientAt dlog01 1 (-1)`,
3. Exact residue sum `(1 : ℂ) + (-1 : ℂ) = 0`. -/
theorem clade_IV_bipolar_simple_pole_residues_and_balance :
    HasSimplePoleCoefficientAt dlog01 0 1 ∧
    HasSimplePoleCoefficientAt dlog01 1 (-1) ∧
    (1 : ℂ) + (-1 : ℂ) = 0 := by
  have h1 := dlog01_hasSimplePoleCoefficientAt_zero
  have h2 := dlog01_hasSimplePoleCoefficientAt_one
  have h3 := dlog01_simplePoleCoefficient_sum_zero
  exact ⟨h1, h2, h3⟩

/-- **Clade V (`clade_V_bost_connes_primon_partition_and_riemann_zeta_euler_product`)**:
Bost–Connes primon partition convergence, zero-temperature Boltzmann decay, and Mathlib's
infinite Euler product for `riemannZeta` (at `M3_ErlangenCasimirMetaLaw` /
`L5_ThermodynamicClosure` / `SenseA`):
1. `Summable (fun p : ℕ => (p : ℝ) ^ (-β))` for `1 < β`,
2. `Tendsto (fun β' : ℝ => (p : ℝ) ^ (-β')) atTop (nhds 0)` for `1 < p`,
3. `infinitePrimeEulerProduct β = riemannZeta (β : ℂ)` for `1 < β`,
4. `finiteMobiusInverseZeta P_reg β = finiteInverseZeta P_reg β`. -/
theorem clade_V_bost_connes_primon_partition_and_riemann_zeta_euler_product
    (P_reg : PrimeRegister) {p : ℕ} (hp : 1 < p) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-β)) ∧
    Tendsto (fun β' : ℝ => (p : ℝ) ^ (-β')) atTop (nhds 0) ∧
    infinitePrimeEulerProduct β = riemannZeta (β : ℂ) ∧
    finiteMobiusInverseZeta P_reg β = finiteInverseZeta P_reg β := by
  have h1 := primon_partition_summable β hβ
  have h2 := boltzmann_factor_tendsto_zero p hp
  have h3 := infinitePrimeEulerProduct_eq_riemannZeta hβ
  have h4 := finiteMobiusInverseZeta_eq_finiteInverseZeta P_reg β
  exact ⟨h1, h2, h3, h4⟩

/-- **Clade VI (`clade_VI_asano_contraction_and_rank_one_factor_localization`)**:
Native algebraic Asano contraction from two-variable affine polynomials
`asanoPoly A B C D z₁ z₂ = A + B z₁ + C z₂ + D z₁ z₂` to `asanoContract A D z = A + D z`
(at `M3_ErlangenCasimirMetaLaw` / `L5_ThermodynamicClosure` / `SenseA`):
1. Non-vanishing constant `A ≠ 0` when `0 ∉ K₁`, `0 ∉ K₂`, and `ZeroFreeOutside K₁ K₂ A B C D`,
2. In the rank-one case `A * D - B * C = 0` with `D ≠ 0`, the factor zeros satisfy
   `-(C / D) ∈ K₁` and `-(A / C) ∈ K₂`. -/
theorem clade_VI_asano_contraction_and_rank_one_factor_localization
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁) (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0) (hdet : A * D - B * C = 0) :
    A ≠ 0 ∧ -(C / D) ∈ K₁ ∧ -(A / C) ∈ K₂ := by
  have h1 := coeff_A_ne_zero_of_zeroFreeOutside h0₁ h0₂ hzf
  have h2 := left_factor_zero_mem_of_rankOne h0₂ hzf hD hdet
  have h3 := right_factor_zero_mem_of_rankOne h0₁ h0₂ hzf hD hdet
  exact ⟨h1, h2, h3⟩

/-- **Clade VII (`clade_VII_bilingual_phase_linear_and_hk_colimit_analyticity`)**:
Bilingual phase-linear map composition (`SenseB`) and filtered direct-limit Krein phase
transport (`SenseD`):
1. Composition of phase-linear continuous linear maps preserves phase-linearity
   (`KX.IsPhaseLinearMap (M.comp L) KZ`),
2. The descended direct-limit phase operator satisfies `J_∞(J_∞ z) = -z` and is injective on
   `AddCommGroup.DirectLimit Stage f`. -/
theorem clade_VII_bilingual_phase_linear_and_hk_colimit_analyticity
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (KX : PhaseStructure X) (KY : PhaseStructure Y) (KZ : PhaseStructure Z)
    {L : X →L[ℝ] Y} {M : Y →L[ℝ] Z}
    (hL : KX.IsPhaseLinearMap L KY) (hM : KY.IsPhaseLinearMap M KZ)
    (Stage : ℕ → Type*) [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    (J : FilteredKreinPhaseFamily Stage f)
    (z : AddCommGroup.DirectLimit Stage f) :
    KX.IsPhaseLinearMap (M.comp L) KZ ∧
    FilteredKreinPhaseFamily.directLimitPhase Stage f J
      (FilteredKreinPhaseFamily.directLimitPhase Stage f J z) = -z ∧
    Function.Injective (FilteredKreinPhaseFamily.directLimitPhase Stage f J) := by
  have h1 := PhaseStructure.comp_phaseLinear KX KY KZ hL hM
  have h2 := FilteredKreinPhaseFamily.directLimitPhase_sq_apply Stage f J z
  have h3 := FilteredKreinPhaseFamily.directLimitPhase_injective Stage f J
  exact ⟨h1, h2, h3⟩

/-- **Clade VIII (`clade_VIII_gns_cuntz_branch_weights_and_operator_dirichlet_spectral_gap`)**:
Axiom-free Cuntz branch-weight equipartition and finite-dimensional operator Dirichlet
Laplacian spectral gap (at `M1_ProjectorClabject` / `L3_Krein` / `SenseA`):
1. Symmetric normalized branch partition `P_L + P_R = I` forces `φ P_L = 1 / 2 ∧ φ P_R = 1 / 2`,
2. Every finite family `T : ι → E →L[ℂ] F` on a finite-dimensional complex Hilbert space `E`
   has a strictly positive spectral gap `c > 0` outside the kernel (`μ = 0 ∨ c ≤ μ.re`). -/
theorem clade_VIII_gns_cuntz_branch_weights_and_operator_dirichlet_spectral_gap
    {A_alg : Type*} [AddMonoid A_alg]
    (φ : A_alg →+ ℝ) (P_L P_R I : A_alg)
    (h_partition : P_L + P_R = I) (h_norm : φ I = 1) (h_symm : φ P_L = φ P_R)
    {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : ι → E →L[ℂ] F) :
    (φ P_L = (1 / 2 : ℝ) ∧ φ P_R = (1 / 2 : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ μ ∈ spectrum ℂ (laplacian T), μ = 0 ∨ c ≤ μ.re) := by
  have h1 := branch_weight_one_half φ P_L P_R I h_partition h_norm h_symm
  have h2 := exists_positive_spectral_gap T
  exact ⟨h1, h2⟩

/-- **Clade IX (`clade_IX_clifford_wavelet_plancherel_and_noncommutative_uncertainty`)**:
Vector-valued Schwartz Fourier Plancherel identity and non-commutative bounded-operator
Robertson uncertainty bound (at `M0_StateIndividual` / `L1_Projective` / `SenseA`):
1. `∫ ξ : V, ‖(FourierTransform.fourier f) ξ‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2`,
2. `|RCLike.im (inner ℂ (centeredOperatorVector A_op ψ) (centeredOperatorVector B_op ψ))| ≤ operatorDeviation A_op ψ * operatorDeviation B_op ψ`. -/
theorem clade_IX_clifford_wavelet_plancherel_and_noncommutative_uncertainty
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : SchwartzMap V H) (A_op B_op : H →L[ℂ] H) (ψ : H) :
    (∫ ξ : V, ‖(FourierTransform.fourier f) ξ‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2) ∧
    |RCLike.im
        (inner ℂ (centeredOperatorVector A_op ψ)
          (centeredOperatorVector B_op ψ))| ≤
      operatorDeviation A_op ψ * operatorDeviation B_op ψ := by
  have h1 := integral_normSq_fourier f
  have h2 := centered_operator_uncertainty A_op B_op ψ
  exact ⟨h1, h2⟩

/-- **Clade X (`clade_X_chiral_analytical_index_grading_inversion_and_splitting`)**:
Finite-dimensional chiral analytical index grading inversion and Dirac chiral decomposition
(at `M1_ProjectorClabject` / `L2_Operator` / `SenseC` / `BucketA`):
1. `analyticalIndex D (-Γ) = -analyticalIndex D Γ`,
2. `chiralPartPlus D Γ + chiralPartMinus D Γ = D`. -/
theorem clade_X_chiral_analytical_index_grading_inversion_and_splitting
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (D Γ : Endomorphism V) :
    analyticalIndex D (-Γ) = -analyticalIndex D Γ ∧
    chiralPartPlus D Γ + chiralPartMinus D Γ = D := by
  have h1 := analyticalIndex_neg_grading_eq_neg D Γ
  have h2 := chiralPartPlus_add_chiralPartMinus D Γ
  exact ⟨h1, h2⟩

set_option linter.style.haveILetI false
/-- **Improper Schwinger / Heat-Kernel Proper-Time Integral on `(0, ∞)`**:
For any positive spectral decay / mass parameter `a > 0`, the improper Lebesgue integral of the
heat-kernel exponential `t ↦ Real.exp (-a * t)` over `Set.Ioi 0` converges to the exact
Schwinger resolvent weight `a⁻¹`:
`∫ t in Set.Ioi 0, Real.exp (-a * t) = a⁻¹`. -/
theorem improper_schwinger_heat_kernel_integral (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi 0, Real.exp (-a * t) = a⁻¹ := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let f : ℝ → ℝ := fun t => (-a⁻¹) * Real.exp (-a * t)
  let f' : ℝ → ℝ := fun t => Real.exp (-a * t)
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt f (f' x) x := by
    intro x _
    have hlin : HasDerivAt (fun t : ℝ => -a * t) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-a * t)) (Real.exp (-a * x) * (-a)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-a * x)).comp x hlin
    have hmul := hexp.const_mul (-a⁻¹)
    convert hmul using 1
    dsimp [f']
    field_simp [ha_ne]
  have hlim : Tendsto f atTop (nhds 0) := by
    have hneg_bot : Tendsto (fun t : ℝ => -a * t) atTop atBot := by
      have h_eq : (fun t : ℝ => -a * t) = (fun t : ℝ => -(a * t)) := by ext t; ring
      rw [h_eq]
      exact tendsto_neg_atBot_iff.mpr ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)
    have hexp_zero : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg_bot
    have hlim0 : Tendsto f atTop (nhds ((-a⁻¹) * 0)) := hexp_zero.const_mul (-a⁻¹)
    simpa using hlim0
  have hint : MeasureTheory.IntegrableOn f' (Set.Ioi 0) := by
    apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (a := 0) (g := f) (g' := f') hderiv
    · intro x _
      exact Real.exp_nonneg (-a * x)
    · exact hlim
  have hEq := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (f := f) (f' := f') hderiv hint hlim
  simpa [f, f'] using hEq
set_option linter.style.haveILetI true

/-- **Operator-Valued Improper Schwinger / Heat-Kernel Bochner Integral on `(0, ∞)`**:
In any complete real normed vector space `E`, integrating the heat-kernel weight
`Real.exp (-a * t) • X` over proper time `t ∈ (0, ∞)` yields the Schwinger resolvent
`a⁻¹ • X`. -/
theorem improper_schwinger_operator_heat_kernel_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E) (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi 0, Real.exp (-a * t) • X = a⁻¹ • X := by
  rw [integral_smul_const, improper_schwinger_heat_kernel_integral a ha]

/-- **Clade X Upgraded (`clade_X_improper_heat_kernel_schwinger_resolvent_and_chiral_supertrace_bridge`)**:
Bridges Clade X's chiral analytical index (`analyticalIndex`, `chiralPartPlus`, `chiralPartMinus`)
with genuine Mathlib improper Bochner/Lebesgue proper-time integration on `Set.Ioi 0` (`SenseA` +
`SenseC`, `BucketA_GenuineNativeMathlibAnalysis`):
1. Grading inversion `analyticalIndex D (-Γ) = -analyticalIndex D Γ` and chiral splitting
   `chiralPartPlus D Γ + chiralPartMinus D Γ = D`,
2. Scalar improper Schwinger heat-kernel integral `∫ t in Set.Ioi 0, Real.exp (-a * t) = a⁻¹`,
3. Operator-valued Bochner improper integral for the Wheeler–Gödel–Connes fluctuated Lichnerowicz
   Laplacian `Ω_sq • genV P A C + κ_sq • (genSig P A C * genSig P A C)` on `Matrix n n ℂ`:
   `∫ t in Set.Ioi 0, Real.exp (-a * t) • (Ω_sq • genV P A C + κ_sq • (genSig P A C * genSig P A C)) = a⁻¹ • (Ω_sq • genV P A C + κ_sq • (genSig P A C * genSig P A C))`,
4. Improper proper-time McKean–Singer supertrace vanishing for any operator `X_odd : Matrix n n ℂ`:
   the commutator `OperatorAlgebra.PeirceSpine.comm (invS P) X_odd` has vanishing improper
   heat-kernel trace integral on `(0, ∞)`:
   `∫ t in Set.Ioi 0, Real.exp (-a * t) * (Matrix.trace (OperatorAlgebra.PeirceSpine.comm (invS P) X_odd)).re = 0`. -/
theorem clade_X_improper_heat_kernel_schwinger_resolvent_and_chiral_supertrace_bridge
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (D Γ : Endomorphism V)
    {n : Type*} [Fintype n] [DecidableEq n]
    (P A C X_odd : Matrix n n ℂ) (a Ω_sq κ_sq : ℝ) (ha : 0 < a) :
    (analyticalIndex D (-Γ) = -analyticalIndex D Γ ∧
     chiralPartPlus D Γ + chiralPartMinus D Γ = D) ∧
    (∫ t in Set.Ioi 0, Real.exp (-a * t) = a⁻¹) ∧
    (∫ t in Set.Ioi 0,
      Real.exp (-a * t) •
        (Ω_sq • genV P A C + κ_sq • (genSig P A C * genSig P A C)) =
      a⁻¹ • (Ω_sq • genV P A C + κ_sq • (genSig P A C * genSig P A C))) ∧
    (∫ t in Set.Ioi 0,
      Real.exp (-a * t) *
        (Matrix.trace (OperatorAlgebra.PeirceSpine.comm (invS P) X_odd)).re = 0) := by
  have htr_comm : (Matrix.trace (OperatorAlgebra.PeirceSpine.comm (invS P) X_odd)).re = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (invS P) X_odd, sub_self, Complex.zero_re]
  refine ⟨⟨analyticalIndex_neg_grading_eq_neg D Γ,
           chiralPartPlus_add_chiralPartMinus D Γ⟩,
          improper_schwinger_heat_kernel_integral a ha,
          improper_schwinger_operator_heat_kernel_integral
            (Ω_sq • genV P A C + κ_sq • (genSig P A C * genSig P A C)) a ha,
          ?_⟩
  simp [htr_comm]

/-!
## Part IV: Concrete Non-Commutative `2 × 2` Complex Matrix Realization & Master Synthesis
-/

/-- Concrete rank-1 Hermitian projector `P = E₀₀` in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def witnessP : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, 0]

/-- Concrete off-diagonal matrix `A = E₀₁` in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def witnessA : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 0, 0]

/-- `witnessP` and `witnessA` do not commute (`witnessP * witnessA ≠ witnessA * witnessP`),
certifying non-commutativity of the concrete operator-analytic witness (`Trap T16`). -/
theorem witnessP_witnessA_noncomm :
    witnessP * witnessA ≠ witnessA * witnessP := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [witnessP, witnessA, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- `witnessP` is idempotent (`witnessP * witnessP = witnessP`). -/
theorem witnessP_idempotent : witnessP * witnessP = witnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessP, Matrix.mul_apply, Fin.sum_univ_two]

/-- `witnessP` is self-adjoint (`star witnessP = witnessP`). -/
theorem witnessP_selfAdjoint : star witnessP = witnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessP, Matrix.star_apply]

/-- The concrete noncommutative witness contains a nonzero square-zero Peirce
component: for `P = E₀₀` and `A = E₀₁`, `conePlus P A = E₀₁`, while
`E₀₁ * E₀₁ = 0`. This is a finite matrix identity, not an infinitesimal or
limit statement. -/
theorem witness_conePlus_nonzero_square_zero :
    conePlus witnessP witnessA ≠ 0 ∧
      conePlus witnessP witnessA * conePlus witnessP witnessA = 0 := by
  refine ⟨?_, by peirce_nf witnessP_idempotent⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp only [conePlus, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.zero_apply, Fin.sum_univ_two] at h01
  norm_num [witnessP, witnessA] at h01

/-- The chiral solder mode `genPhi witnessP witnessA (star witnessA)` is nonzero. -/
theorem witness_genPhi_ne_zero :
    genPhi witnessP witnessA (star witnessA) ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp only [genPhi, conePlus, coneMinus, Matrix.add_apply, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.star_apply, Matrix.zero_apply,
    Fin.sum_univ_two] at h01
  norm_num [witnessP, witnessA] at h01

/-- Concrete non-commutative `2 × 2` matrix theorem: `witnessP` and `witnessA` fail to commute,
and the improper BKM resolvent trace integral of their chiral solder mode
`genPhi witnessP witnessA (star witnessA)` is strictly positive for all `p, q > 0`. -/
theorem witness_noncommutative_bkm_trace_integral_pos
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    witnessP * witnessA ≠ witnessA * witnessP ∧
    0 < ∫ s in Set.Ioi 0,
      (Matrix.trace
        (genPhi witnessP witnessA (star witnessA) *
          sheetResolvent p q s witnessP *
          genPhi witnessP witnessA (star witnessA) *
          sheetResolvent p q s witnessP)).re := by
  have hNoncomm := witnessP_witnessA_noncomm
  have hPos :=
    bkm_real_trace_resolvent_integral_pos_of_mode_ne
      witnessP witnessA witnessP_idempotent witnessP_selfAdjoint
      witness_genPhi_ne_zero p q hp hq
  exact ⟨hNoncomm, hPos⟩

/-- **Master Coagulated Synthesis of the Analytic Ontology, 10-Clade Taxonomy & 8-Epoch Phylogenesis**:
Unites in one kernel-checked statement:
1. **Ontology & Non-Conflation**: Pairwise distinctness of the 4 semantic senses of "analytic"
   (`AnalyticSemanticSense.pairwise_distinct`), acyclicity of `OntologyMetaLevel.instantiatesEdge_acyclic`,
   acyclicity of `AnalyticPhylogeneticEpoch.causalEdge_acyclic`, and Bucket-C exclusion across
   all 10 active clades (`AnalyticTaxonomicClade.active_clade_not_bucketC`),
2. **Clades I & II (Non-Commutative Matrix Log-Det Fréchet Calculus & Improper BKM Integrals)**:
   `HasFDerivAt` of `quadraticLogVolume`, trace-pairing resolvent force, improper BKM operator
   Bochner integral `bkm_resolvent_integral_factorized`, and initial-response identity
   `quadraticLogVolume_initial_response_eq_isotropic_bkm`,
3. **Clades III, IV, V & VI (Dikin Barrier Hessians, Bipolar Residues, Zeta Euler Product & Asano Contraction)**:
   `souriauBarrier_hessian_metric`, `orbitBarrier_hessian_metric`, `dlog01` simple-pole residues,
   `primon_partition_summable`, `infinitePrimeEulerProduct_eq_riemannZeta`, and rank-one Asano
   factor localization,
4. **Clades VII, VIII, IX & X (Bilingual/HK Colimit Phase, GNS/Dirichlet Gap, Wavelet Plancherel & Chiral Index)**:
   `PhaseStructure.comp_phaseLinear`, `directLimitPhase_sq_apply`, `branch_weight_one_half`,
   `exists_positive_spectral_gap`, `integral_normSq_fourier`, `centered_operator_uncertainty`,
   and `analyticalIndex_neg_grading_eq_neg`,
5. **Non-Commutative `2 × 2` Complex Matrix Witness**: `witnessP * witnessA ≠ witnessA * witnessP`,
   a nonzero square-zero Peirce component, and a strictly positive improper BKM resolvent trace
   integral. -/
theorem analytic_ontology_taxonomy_phylogenesis_master_synthesis
    {n : Type*} [Fintype n] [DecidableEq n]
    (β : ℝ) (Φ H P A C : Matrix n n ℂ)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ)))
    (hP : P * P = P)
    (p q ξ x v : ℝ) (hp : 0 < p) (hq : 0 < q) (hx : 0 < x)
    (P_reg : PrimeRegister) {p_nat : ℕ} (hp_nat : 1 < p_nat) {β_zeta : ℝ} (hβ_zeta : 1 < β_zeta)
    {K₁ K₂ : Set ℂ} {A_asano B_asano C_asano D_asano : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁) (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A_asano B_asano C_asano D_asano)
    (hD_asano : D_asano ≠ 0) (hdet_asano : A_asano * D_asano - B_asano * C_asano = 0)
    (Stage : ℕ → Type*) [∀ m, AddCommGroup (Stage m)]
    (f_stage : ∀ m k : ℕ, m ≤ k → Stage m →+ Stage k)
    (J_phase : FilteredKreinPhaseFamily Stage f_stage)
    (z_lim : AddCommGroup.DirectLimit Stage f_stage)
    {V_ind : Type*} [AddCommGroup V_ind] [Module ℝ V_ind] [FiniteDimensional ℝ V_ind]
    (D_dirac Γ_dirac : Endomorphism V_ind) :
    -- 1. Multi-Level Ontology, 4 Semantic Senses, 10 Clades, 8-Epoch Phylogenesis & 8-Stage Poset:
    ((∀ L : OntologyMetaLevel, ¬ Relation.TransGen OntologyMetaLevel.instantiatesEdge L L) ∧
     (∀ E_ep : AnalyticPhylogeneticEpoch,
        ¬ Relation.TransGen AnalyticPhylogeneticEpoch.causalEdge E_ep E_ep) ∧
     (∀ S_st : AnalyticArchetypeStage,
        ¬ Relation.TransGen AnalyticArchetypeStage.causalEdge S_st S_st) ∧
     (∀ c : AnalyticTaxonomicClade,
        c.qmsBucket ≠ .BucketC_SupersededHistoricalSurrogate)) ∧
    -- 2. Clades I & II (Matrix LogDet Fréchet Calculus & Improper BKM Integrals):
    (HasFDerivAt (fun X : Matrix n n ℂ => quadraticLogVolume β X)
       (quadraticLogVolumeDifferential β Φ) Φ ∧
     quadraticLogVolumeDifferential β Φ H =
       (Matrix.trace (quadraticLogVolumeResolventForce β Φ * H)).re ∧
     (∫ s in Set.Ioi 0,
        genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
        bkmDividedDiffWeight p q • genV P A C) ∧
     deriv (fun β' : ℝ => quadraticLogVolume β' (genPhi P A C)) 0 =
       ∫ s in Set.Ioi 0,
         (Matrix.trace
           (genPhi P A C * sheetResolvent 1 1 s P * genPhi P A C *
             sheetResolvent 1 1 s P)).re) ∧
    -- 3. Clades III, IV, V & VI (Dikin Hessians, Bipolar Residues, Zeta Euler Product & Asano):
    (hessianMap souriauBarrier ξ v v = (2 / Real.cosh ξ ^ 2) * v ^ 2 ∧
     hessianMap orbitBarrier x v v = (1 / x ^ 2) * v ^ 2 ∧
     HasSimplePoleCoefficientAt dlog01 0 1 ∧
     HasSimplePoleCoefficientAt dlog01 1 (-1) ∧
     Summable (fun k : ℕ => (k : ℝ) ^ (-β_zeta)) ∧
     Tendsto (fun β' : ℝ => (p_nat : ℝ) ^ (-β')) atTop (nhds 0) ∧
     infinitePrimeEulerProduct β_zeta = riemannZeta (β_zeta : ℂ) ∧
     finiteMobiusInverseZeta P_reg β_zeta = finiteInverseZeta P_reg β_zeta ∧
     -(C_asano / D_asano) ∈ K₁ ∧ -(A_asano / C_asano) ∈ K₂) ∧
    -- 4. Clades VII & X (Filtered Direct-Limit Krein Phase & Chiral Analytical Index):
    (FilteredKreinPhaseFamily.directLimitPhase Stage f_stage J_phase
       (FilteredKreinPhaseFamily.directLimitPhase Stage f_stage J_phase z_lim) = -z_lim ∧
     Function.Injective (FilteredKreinPhaseFamily.directLimitPhase Stage f_stage J_phase) ∧
     analyticalIndex D_dirac (-Γ_dirac) = -analyticalIndex D_dirac Γ_dirac ∧
     chiralPartPlus D_dirac Γ_dirac + chiralPartMinus D_dirac Γ_dirac = D_dirac) ∧
    -- 5. Non-Commutative 2×2 Matrix Witness and its Peirce Nilpotent:
    (witnessP * witnessA ≠ witnessA * witnessP ∧
     (conePlus witnessP witnessA ≠ 0 ∧
       conePlus witnessP witnessA * conePlus witnessP witnessA = 0) ∧
     0 < ∫ s in Set.Ioi 0,
       (Matrix.trace
         (genPhi witnessP witnessA (star witnessA) *
           sheetResolvent p q s witnessP *
           genPhi witnessP witnessA (star witnessA) *
           sheetResolvent p q s witnessP)).re) := by
  have hAsano :=
    clade_VI_asano_contraction_and_rank_one_factor_localization
      h0₁ h0₂ hzf hD_asano hdet_asano
  exact ⟨⟨OntologyMetaLevel.instantiatesEdge_acyclic,
          AnalyticPhylogeneticEpoch.causalEdge_acyclic,
          AnalyticArchetypeStage.causalEdge_acyclic,
          AnalyticTaxonomicClade.active_clade_not_bucketC⟩,
         ⟨hasFDerivAt_quadraticLogVolume β Φ hM,
          quadraticLogVolumeDifferential_apply β Φ H hM,
          bkm_resolvent_integral_factorized P A C hP p q hp hq,
          quadraticLogVolume_initial_response_eq_isotropic_bkm P A C hP⟩,
         ⟨souriauBarrier_hessian_metric ξ v,
          orbitBarrier_hessian_metric x v hx,
          dlog01_hasSimplePoleCoefficientAt_zero,
          dlog01_hasSimplePoleCoefficientAt_one,
          primon_partition_summable β_zeta hβ_zeta,
          boltzmann_factor_tendsto_zero p_nat hp_nat,
          infinitePrimeEulerProduct_eq_riemannZeta hβ_zeta,
          finiteMobiusInverseZeta_eq_finiteInverseZeta P_reg β_zeta,
          hAsano.2.1,
          hAsano.2.2⟩,
         ⟨FilteredKreinPhaseFamily.directLimitPhase_sq_apply Stage f_stage J_phase z_lim,
          FilteredKreinPhaseFamily.directLimitPhase_injective Stage f_stage J_phase,
          analyticalIndex_neg_grading_eq_neg D_dirac Γ_dirac,
          chiralPartPlus_add_chiralPartMinus D_dirac Γ_dirac⟩,
         ⟨witnessP_witnessA_noncomm, witness_conePlus_nonzero_square_zero,
          bkm_real_trace_resolvent_integral_pos_of_mode_ne
            witnessP witnessA witnessP_idempotent witnessP_selfAdjoint
            witness_genPhi_ne_zero p q hp hq⟩⟩

/-!
## Part V: Gravito-Electromagnetic (GEM) 10-Clade Taxonomy & 8-Epoch Phylogenesis
-/

/-- The 10 taxonomic clades of the non-commutative Peirce-spine gravito-electromagnetic (GEM)
algebraic formalism across `lean/InfoGeometry/`. -/
inductive GEMTaxonomicClade : Type
  | GCladeI_GravitoElectricMonopole
  | GCladeII_GravitoMagneticDipole
  | GCladeIII_LenseThirringCoriolis
  | GCladeIV_WorkFreeCoriolis
  | GCladeV_SecondOrderCentrifugal
  | GCladeVI_KerrErgosphere
  | GCladeVII_EinsteinCartanTorsion
  | GCladeVIII_OnsagerReciprocity
  | GCladeIX_ChiralSplitting
  | GCladeX_MachPrinciple
  deriving DecidableEq, Repr, Inhabited

/-- Primary semantic sense of each GEM taxonomic clade. -/
def gemPrimarySense : GEMTaxonomicClade → AnalyticSemanticSense
  | .GCladeI_GravitoElectricMonopole => .SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | .GCladeII_GravitoMagneticDipole  => .SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | .GCladeIII_LenseThirringCoriolis => .SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | .GCladeIV_WorkFreeCoriolis       => .SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | .GCladeV_SecondOrderCentrifugal  => .SenseB_PhaseLinearCauchyRiemannHestenesKrein
  | .GCladeVI_KerrErgosphere         => .SenseD_FilteredColimitFiniteStageContinuumTransport
  | .GCladeVII_EinsteinCartanTorsion => .SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac
  | .GCladeVIII_OnsagerReciprocity   => .SenseA_NativeMathlibDifferentialIntegralOperator
  | .GCladeIX_ChiralSplitting        => .SenseC_ChiralAnalyticalIndexAtiyahSingerBottDirac
  | .GCladeX_MachPrinciple           => .SenseD_FilteredColimitFiniteStageContinuumTransport

/-- QMS audit bucket of each GEM taxonomic clade. -/
def gemQMSBucket : GEMTaxonomicClade → AnalyticQMSBucket
  | .GCladeI_GravitoElectricMonopole => .BucketA_GenuineNativeMathlibAnalysis
  | .GCladeII_GravitoMagneticDipole  => .BucketA_GenuineNativeMathlibAnalysis
  | .GCladeIII_LenseThirringCoriolis => .BucketA_GenuineNativeMathlibAnalysis
  | .GCladeIV_WorkFreeCoriolis       => .BucketA_GenuineNativeMathlibAnalysis
  | .GCladeV_SecondOrderCentrifugal  => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .GCladeVI_KerrErgosphere         => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .GCladeVII_EinsteinCartanTorsion => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .GCladeVIII_OnsagerReciprocity   => .BucketA_GenuineNativeMathlibAnalysis
  | .GCladeIX_ChiralSplitting        => .BucketA_GenuineNativeMathlibAnalysis
  | .GCladeX_MachPrinciple           => .BucketB_HonestAlgebraicFiniteStageColimitTransport

/-- Multi-level ontology stratum (`M0` → `M3`) of each GEM clade. -/
def gemMetaLevel : GEMTaxonomicClade → OntologyMetaLevel
  | .GCladeI_GravitoElectricMonopole => .M2_GrassmannianPowertypeOrbit
  | .GCladeII_GravitoMagneticDipole  => .M3_ErlangenCasimirMetaLaw
  | .GCladeIII_LenseThirringCoriolis => .M3_ErlangenCasimirMetaLaw
  | .GCladeIV_WorkFreeCoriolis       => .M2_GrassmannianPowertypeOrbit
  | .GCladeV_SecondOrderCentrifugal  => .M3_ErlangenCasimirMetaLaw
  | .GCladeVI_KerrErgosphere         => .M3_ErlangenCasimirMetaLaw
  | .GCladeVII_EinsteinCartanTorsion => .M3_ErlangenCasimirMetaLaw
  | .GCladeVIII_OnsagerReciprocity   => .M2_GrassmannianPowertypeOrbit
  | .GCladeIX_ChiralSplitting        => .M2_GrassmannianPowertypeOrbit
  | .GCladeX_MachPrinciple           => .M3_ErlangenCasimirMetaLaw

/-- Representation-depth layer (`L0` → `L5`) of each GEM clade. -/
def gemRepDepth : GEMTaxonomicClade → RepDepth
  | .GCladeI_GravitoElectricMonopole => .operator
  | .GCladeII_GravitoMagneticDipole  => .krein
  | .GCladeIII_LenseThirringCoriolis => .transport
  | .GCladeIV_WorkFreeCoriolis       => .transport
  | .GCladeV_SecondOrderCentrifugal  => .transport
  | .GCladeVI_KerrErgosphere         => .krein
  | .GCladeVII_EinsteinCartanTorsion => .operator
  | .GCladeVIII_OnsagerReciprocity   => .thermo
  | .GCladeIX_ChiralSplitting        => .operator
  | .GCladeX_MachPrinciple           => .projective

/-- Every active GEM taxonomic clade is classified in either Bucket A or Bucket B, with zero
active clades in Bucket C. -/
theorem gemActive_clade_not_bucketC (c : GEMTaxonomicClade) :
    gemQMSBucket c ≠ .BucketC_SupersededHistoricalSurrogate := by
  cases c <;> decide

/-- The 8 phylogenetic epochs of the GEM non-commutative algebraic formalism. -/
inductive GEMPhylogeneticEpoch : Type
  | GEpoch1_NewtonianGravitoElectric
  | GEpoch2_MachRelationalInertia
  | GEpoch3_LenseThirring1918
  | GEpoch4_GravitoElectromagneticSplit
  | GEpoch5_WeylSpinorChiralSplit
  | GEpoch6_CommutatorAlgebra
  | GEpoch7_SecondOrderCentrifugal
  | GEpoch8_KerrErgosphereCollapse
  deriving DecidableEq, Repr, Inhabited

/-- Strictly monotone integer rank (`1` through `8`) for `GEMPhylogeneticEpoch`. -/
def gemEpochRank : GEMPhylogeneticEpoch → ℕ
  | .GEpoch1_NewtonianGravitoElectric    => 1
  | .GEpoch2_MachRelationalInertia       => 2
  | .GEpoch3_LenseThirring1918           => 3
  | .GEpoch4_GravitoElectromagneticSplit => 4
  | .GEpoch5_WeylSpinorChiralSplit       => 5
  | .GEpoch6_CommutatorAlgebra           => 6
  | .GEpoch7_SecondOrderCentrifugal      => 7
  | .GEpoch8_KerrErgosphereCollapse      => 8

/-- Directed causal dependency edge `e₁ ≺ e₂` between GEM phylogenetic epochs. -/
def gemCausalEdge : GEMPhylogeneticEpoch → GEMPhylogeneticEpoch → Prop :=
  fun e₁ e₂ => e₁ ≠ e₂ ∧ gemEpochRank e₁ < gemEpochRank e₂

/-- Irreflexivity of the GEM phylogenetic causal relation. -/
theorem gemCausalEdge_irrefl (e : GEMPhylogeneticEpoch) :
    ¬ gemCausalEdge e e := by
  intro h
  exact Nat.lt_irrefl (gemEpochRank e) h.2

/-- Transitivity of the GEM phylogenetic causal relation. -/
theorem gemCausalEdge_trans {e₁ e₂ e₃ : GEMPhylogeneticEpoch}
    (h₁₂ : gemCausalEdge e₁ e₂) (h₂₃ : gemCausalEdge e₂ e₃) :
    gemCausalEdge e₁ e₃ := by
  have hlt : gemEpochRank e₁ < gemEpochRank e₃ :=
    Nat.lt_trans h₁₂.2 h₂₃.2
  refine ⟨?_, hlt⟩
  intro heq
  rw [heq] at hlt
  exact Nat.lt_irrefl (gemEpochRank e₃) hlt

/-- Asymmetry (two-cycle acyclicity) of the GEM phylogenetic causal relation. -/
theorem gemCausalEdge_acyclic {e₁ e₂ : GEMPhylogeneticEpoch}
    (h₁₂ : gemCausalEdge e₁ e₂) :
    ¬ gemCausalEdge e₂ e₁ := by
  intro h₂₁
  exact Nat.lt_asymm h₁₂.2 h₂₁.2

/-- Order-preserving bijection from the 8-epoch `AnalyticPhylogeneticEpoch` cladogram
to the 8-epoch `GEMPhylogeneticEpoch` cladogram. -/
def analyticToGEMEpoch : AnalyticPhylogeneticEpoch → GEMPhylogeneticEpoch
  | .Epoch1_ScalarConvexAndExponentialFamilyGenesis               => .GEpoch1_NewtonianGravitoElectric
  | .Epoch2_BostConnesPrimonAndChiralAnalyticalIndex              => .GEpoch2_MachRelationalInertia
  | .Epoch3_BilingualPhaseLinearityAndColimitBifurcation          => .GEpoch3_LenseThirring1918
  | .Epoch4_ZetaEulerProductsMellinLaplaceAndWavelets             => .GEpoch4_GravitoElectromagneticSplit
  | .Epoch5_GNSCuntzHilbertSpacesAndBipolarContourRadiation       => .GEpoch5_WeylSpinorChiralSplit
  | .Epoch6_NonCommutativeMatrixLogDetFrechetAndOperatorDirichlet => .GEpoch6_CommutatorAlgebra
  | .Epoch7_AntiVacuityPurificationAndBoundaryHonesty             => .GEpoch7_SecondOrderCentrifugal
  | .Epoch8_OperatorSurprisalBKMIntegralsAndUnifiedDikinSynthesis => .GEpoch8_KerrErgosphereCollapse

/-- Exact rank shift `gemEpochRank (analyticToGEMEpoch u) = u.rank + 1`. -/
theorem analyticToGEMEpoch_rank_eq (u : AnalyticPhylogeneticEpoch) :
    gemEpochRank (analyticToGEMEpoch u) = u.rank + 1 := by
  cases u <;> rfl

/-- Injectivity of `analyticToGEMEpoch`. -/
theorem analyticToGEMEpoch_injective : Function.Injective analyticToGEMEpoch := by
  intro u v h
  cases u <;> cases v <;> first | rfl | cases h

/-- Order-homomorphism property: `analyticToGEMEpoch` maps every causal edge `u ≺ v` in
`AnalyticPhylogeneticEpoch` to a causal edge `gemCausalEdge` in `GEMPhylogeneticEpoch`. -/
theorem analyticToGEMEpoch_preserves_causalEdge {u v : AnalyticPhylogeneticEpoch}
    (h : AnalyticPhylogeneticEpoch.causalEdge u v) :
    gemCausalEdge (analyticToGEMEpoch u) (analyticToGEMEpoch v) := by
  refine ⟨?_, ?_⟩
  · intro heq
    have huv := analyticToGEMEpoch_injective heq
    subst huv
    exact Nat.lt_irrefl u.rank h
  · rw [analyticToGEMEpoch_rank_eq, analyticToGEMEpoch_rank_eq]
    exact Nat.add_lt_add_right h 1

end InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset
