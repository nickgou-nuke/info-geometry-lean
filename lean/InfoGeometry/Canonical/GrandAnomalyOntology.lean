/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.AnomalyOntology
import InfoGeometry.Canonical.GenericObliqueIdempotentAnomaly
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset
import InfoGeometry.Canonical.SouriauBostConnesTransition
import InfoGeometry.Canonical.ChiralCuntzSuperchargeBridge
import InfoGeometry.Canonical.ChiralCuntzAnomalyPartitionBridge
import InfoGeometry.Canonical.GreenSchwarzAnomalyInflowBridge
import InfoGeometry.Canonical.WittenParityAnomalyBridge
import InfoGeometry.Canonical.O55BottAnomalyClosure
import InfoGeometry.Canonical.O55FiveGradeClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelChiralBlockAnomalyGapPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectPeirceChargeAnomaly
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly
import VirasoroProject.Extensions.PrimeVirasoroSugawara
import Omega.Folding.GaugeAnomalyJordanFingerprint
import Omega.POM.AnomCohomologyClass
import Omega.Zeta.FinitePartMomentAnomalyReducedDeterminantRatio
import Omega.CircleDimension.AnomalyQuadraticLaw
import Omega.Conclusion.AnomalyQuotientCanonicalHilbertization
import Omega.GU.Window6ThreeFamilyZeroAnom
import InfoGeometry.Algebra.NonAssocIteratedLeibniz
import InfoGeometry.Algebra.OctonionMatrixObstruction
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Arithmetic.BostConnesCriticality
import InfoGeometry.Meta

/-!
# Grand Anomaly Ontology, Multi-Clade Taxonomy, and Repository-Wide Code Reconciliation

This module constructs the comprehensive **Grand Anomaly Ontology** across `info-geometry-lean`,
expanding `AnomalyOntology.lean` to reconcile all nine active anomaly corridors across
`lean/InfoGeometry/**`, `VirasoroProject/**`, and `lean/Omega/**` with complete native Mathlib
carriers, de-conflated structural theorems, and direct projections from existing repository owners.

## Taxonomic Architecture (9 Clades)

1. **Clade I — Oblique Idempotent Defect** (`GenericObliqueIdempotentAnomaly`):
   Ring-theoretic oblique perturbation $P_{\mathrm{obl}} = P + P X (1-P)$ and $[P_{\mathrm{obl}}, P] = -P X (1-P)$,
   instantiated by $[P_{\mathrm{obl}}, P_L] = -E_{01}$.
2. **Clade II — Topological Index & Projective Poset** (`FreedWickReflectionAndTopologicalIndexPoset`, `WittenParityAnomalyBridge`):
   Dan Freed 6-node diamond poset, $V_4$ projective 2-cocycle, doubled Kronecker cancellation,
   Krein BRST nilpotent differential $Q = E_{01}$, general $n \times n$ McKean-Singer supertrace doubling
   and even-power vanishing, $\mathrm{Pin}^{\pm}$ reflection parity flip, and analytic $\mu_{16}$ Witten $\eta$-phase.
3. **Clade III — Concrete Hilbert Sewn Boundary** (`ConcreteHilbertSewnAnomaly`):
   Completed Cantor Hilbert space $H_{lp} E$, $\mathrm{Cl}(1,1)$ anticommuting modular swap $J_{lp} \varepsilon_{lp} = -\varepsilon_{lp} J_{lp}$,
   Cuntz $O_2$ non-commuting branch sewing invariance $J S_i J = S_i$, exact boundary cancellation.
4. **Clade IV — Souriau-Bost-Connes Modular Transition** (`SouriauBostConnesTransition`):
   KMS thermal modular flow with Liouville parity protection $[\Gamma, \sigma_t] = 0$,
   Witten index reciprocal zeta $L \nearrow \mu(\beta) = \zeta(\beta)^{-1}$, zero-temperature boundary crystallization.
5. **Clade V — Bulk-Boundary Inflow & Gauge Cancellation** (`GreenSchwarzAnomalyInflowBridge`, `ChiralCuntzSuperchargeBridge`, `ChiralCuntzAnomalyPartitionBridge`):
   Bulk Chern-Simons inflow cancellation $\delta S_{\mathrm{bulk}} + \mathcal{A}_{\mathrm{boundary}} = 0$,
   anomalous Bianchi transgression $d(dB - \Omega_{\mathrm{CS}}) = -\operatorname{tr}(F \wedge F)$,
   Kugo-Ojima BRST supercharge exactness, and Cantor branch-chirality trace vanishing.
6. **Clade VI — Graded Lie TKK & O(5,5) T-Duality Closure** (`O55BottAnomalyClosure`, `O55FiveGradeClosure`):
   Genuine $10 \times 10$ split-orthogonal $\mathfrak{so}(5,5)$ 5-graded contact Heisenberg Lie carrier
   ($[P_{+1}, Q_{+1}] = Z_{+2} \ne 0$, $[Z_{-2}, Z_{+2}] = H_{\mathrm{contact}}$), Buscher $O(5,5)$ T-duality
   involution $T Z_{\pm 2} T = Z_{\mp 2}$, 5D Hodge bivector-associator coincidence $\binom{5}{2} = \binom{5}{3} = 10$,
   conformal $\mathfrak{so}(5,5)$ grade-$\pm 2$ closure, and $\mathrm{Cl}(5,5)$ Bott periodicity.
7. **Clade VII — Peirce Spine Einstein-Cartan Frame Dragging** (`DefectPeirceChargeAnomaly`, `KantorCornerAnomaly`, `MultiChannelChiralBlockAnomalyGapPoset`):
   Idempotency curvature defect $\delta = V^2 - V$, deformed $\mathrm{Cl}(1,1)$ Peirce algebra ($\Phi^2 = V$, $J^2 = -V$, $\Sigma^2 = V + \delta(V)$),
   Chiral Einstein Anomaly $S_P [\Phi, J] = -2V$, spin frame dragging $[\Sigma, \Phi] = 2VJ$,
   Kantor-Jordan associator $\mathcal{A}_\bullet(N_-, N_+, N_+) = 2VN_+$, extreme Peirce charge defects, and multi-channel gap additivity.
8. **Clade VIII — Quantum Geometric Tensor & Conformal Virasoro** (`PrimeVirasoroSugawara`):
   Universal `InnerProductSpace ℂ` Robertson-Schrödinger QGT bound $\frac{1}{4}\|\langle \psi, [A,B]\psi \rangle\|^2 \le \|(A-a)\psi\|^2 \|(B-b)\psi\|^2$,
   $\mathbb{C}^2$ Bloch purity and exact QGT variance-curvature defect, Virasoro Sugawara central extension $[J_1, J_{-1}] = K$ ($c = 1$),
   and Gelfand-Fuks 2-cocycle cohomology $H^2(\mathcal{W}, \mathbb{Q}) \ne 0$ with $\mathfrak{sl}_2$ anomaly-freeness.
9. **Clade IX — Omega Analytic Moment Folding & Witten Index** (`lean/Omega/**`):
   Injective equivariant BRST-Jordan intertwiner into the Parry transfer defect, canonical radical-quotient
   non-degenerate descent, reduced determinant ratio logarithmic law, canonical quotient Hilbertization,
   unique positive Rank-3 Hodge self-duality $\binom{r}{2} = r \iff r = 3$, and Window-6 ($\binom{4}{2} = 6$)
   three-family / $N_c = 3$ chiral gauge anomaly cancellation.

Strict proof integrity: Zero `sorry`, zero `admit`, foundational axioms only (`propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section

open scoped Matrix
open scoped Topology
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation

open Matrix
open InfoGeometry.Meta
open InfoGeometry.MetaCompiler
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Canonical.AnomalyOntology
open InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset
open ChiralCuntzSuperchargeBridge
open InfoGeometry.Canonical.ChiralCuntzAnomalyPartitionBridge
open InfoGeometry.Canonical.GreenSchwarzAnomalyInflow

namespace InfoGeometry.Canonical.GrandAnomalyOntology

/-! ## Part I: The Eight Grand Semantic Senses of "Anomaly" -/

/-- The eight distinct mathematical senses in which "anomaly" appears across the repository. -/
inductive GrandAnomalySemanticSense : Type
  | SenseA_ProjectorCommutatorObliqueObstruction
  | SenseB_TopologicalIndexProjectiveCohomology
  | SenseC_InfiniteHilbertBoundarySewing
  | SenseD_ThermodynamicModularKMS
  | SenseE_GradingExtensionHeisenbergCenter
  | SenseF_CurvatureTorsionVielbeinCommutator
  | SenseG_QuantumGeometricUncertainty
  | SenseH_ConformalCentralCharge
  deriving DecidableEq, Repr, Inhabited

namespace GrandAnomalySemanticSense

/-- Numerical discriminator (`0` through `7`) for the eight semantic senses of "anomaly". -/
def code : GrandAnomalySemanticSense → ℕ
  | .SenseA_ProjectorCommutatorObliqueObstruction => 0
  | .SenseB_TopologicalIndexProjectiveCohomology  => 1
  | .SenseC_InfiniteHilbertBoundarySewing         => 2
  | .SenseD_ThermodynamicModularKMS               => 3
  | .SenseE_GradingExtensionHeisenbergCenter      => 4
  | .SenseF_CurvatureTorsionVielbeinCommutator    => 5
  | .SenseG_QuantumGeometricUncertainty           => 6
  | .SenseH_ConformalCentralCharge                => 7

/-- The discriminator `code` is injective on `GrandAnomalySemanticSense`. -/
theorem code_injective : Function.Injective code := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- All eight semantic senses are pairwise distinct. -/
theorem pairwise_distinct :
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseB_TopologicalIndexProjectiveCohomology ∧
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseC_InfiniteHilbertBoundarySewing ∧
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseD_ThermodynamicModularKMS ∧
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseE_GradingExtensionHeisenbergCenter ∧
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseF_CurvatureTorsionVielbeinCommutator ∧
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseG_QuantumGeometricUncertainty ∧
    SenseA_ProjectorCommutatorObliqueObstruction ≠ SenseH_ConformalCentralCharge ∧
    SenseB_TopologicalIndexProjectiveCohomology ≠ SenseC_InfiniteHilbertBoundarySewing ∧
    SenseB_TopologicalIndexProjectiveCohomology ≠ SenseD_ThermodynamicModularKMS ∧
    SenseB_TopologicalIndexProjectiveCohomology ≠ SenseE_GradingExtensionHeisenbergCenter ∧
    SenseB_TopologicalIndexProjectiveCohomology ≠ SenseF_CurvatureTorsionVielbeinCommutator ∧
    SenseB_TopologicalIndexProjectiveCohomology ≠ SenseG_QuantumGeometricUncertainty ∧
    SenseB_TopologicalIndexProjectiveCohomology ≠ SenseH_ConformalCentralCharge ∧
    SenseC_InfiniteHilbertBoundarySewing ≠ SenseD_ThermodynamicModularKMS ∧
    SenseC_InfiniteHilbertBoundarySewing ≠ SenseE_GradingExtensionHeisenbergCenter ∧
    SenseC_InfiniteHilbertBoundarySewing ≠ SenseF_CurvatureTorsionVielbeinCommutator ∧
    SenseC_InfiniteHilbertBoundarySewing ≠ SenseG_QuantumGeometricUncertainty ∧
    SenseC_InfiniteHilbertBoundarySewing ≠ SenseH_ConformalCentralCharge ∧
    SenseD_ThermodynamicModularKMS ≠ SenseE_GradingExtensionHeisenbergCenter ∧
    SenseD_ThermodynamicModularKMS ≠ SenseF_CurvatureTorsionVielbeinCommutator ∧
    SenseD_ThermodynamicModularKMS ≠ SenseG_QuantumGeometricUncertainty ∧
    SenseD_ThermodynamicModularKMS ≠ SenseH_ConformalCentralCharge ∧
    SenseE_GradingExtensionHeisenbergCenter ≠ SenseF_CurvatureTorsionVielbeinCommutator ∧
    SenseE_GradingExtensionHeisenbergCenter ≠ SenseG_QuantumGeometricUncertainty ∧
    SenseE_GradingExtensionHeisenbergCenter ≠ SenseH_ConformalCentralCharge ∧
    SenseF_CurvatureTorsionVielbeinCommutator ≠ SenseG_QuantumGeometricUncertainty ∧
    SenseF_CurvatureTorsionVielbeinCommutator ≠ SenseH_ConformalCentralCharge ∧
    SenseG_QuantumGeometricUncertainty ≠ SenseH_ConformalCentralCharge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;> cases h

end GrandAnomalySemanticSense

/-! ## Part II: The Nine Taxonomic Clades of "Grand Anomaly" -/

/-- The nine taxonomic clades of anomaly formalization across the repository. -/
inductive GrandAnomalyTaxonomicClade : Type
  | CladeI_ObliqueIdempotentDefect
  | CladeII_TopologicalIndexProjectivePoset
  | CladeIII_ConcreteHilbertSewnBoundary
  | CladeIV_SouriauBostConnesModularTransition
  | CladeV_BulkBoundaryInflowAndGaugeCancellation
  | CladeVI_GradedLieTKKAndO55TDualityClosure
  | CladeVII_PeirceSpineEinsteinCartanFrameDragging
  | CladeVIII_QuantumGeometricTensorAndConformalVirasoro
  | CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex
  deriving DecidableEq, Repr, Inhabited

namespace GrandAnomalyTaxonomicClade

/-- Numerical index (`0` through `8`) of each grand taxonomic clade. -/
def index : GrandAnomalyTaxonomicClade → ℕ
  | .CladeI_ObliqueIdempotentDefect                       => 0
  | .CladeII_TopologicalIndexProjectivePoset              => 1
  | .CladeIII_ConcreteHilbertSewnBoundary                 => 2
  | .CladeIV_SouriauBostConnesModularTransition           => 3
  | .CladeV_BulkBoundaryInflowAndGaugeCancellation        => 4
  | .CladeVI_GradedLieTKKAndO55TDualityClosure            => 5
  | .CladeVII_PeirceSpineEinsteinCartanFrameDragging      => 6
  | .CladeVIII_QuantumGeometricTensorAndConformalVirasoro => 7
  | .CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex     => 8

/-- The index function `index` is injective on `GrandAnomalyTaxonomicClade`. -/
theorem index_injective : Function.Injective index := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- Primary semantic sense associated with each clade. -/
def semanticSense : GrandAnomalyTaxonomicClade → GrandAnomalySemanticSense
  | .CladeI_ObliqueIdempotentDefect                       => .SenseA_ProjectorCommutatorObliqueObstruction
  | .CladeII_TopologicalIndexProjectivePoset              => .SenseB_TopologicalIndexProjectiveCohomology
  | .CladeIII_ConcreteHilbertSewnBoundary                 => .SenseC_InfiniteHilbertBoundarySewing
  | .CladeIV_SouriauBostConnesModularTransition           => .SenseD_ThermodynamicModularKMS
  | .CladeV_BulkBoundaryInflowAndGaugeCancellation        => .SenseB_TopologicalIndexProjectiveCohomology
  | .CladeVI_GradedLieTKKAndO55TDualityClosure            => .SenseE_GradingExtensionHeisenbergCenter
  | .CladeVII_PeirceSpineEinsteinCartanFrameDragging      => .SenseF_CurvatureTorsionVielbeinCommutator
  | .CladeVIII_QuantumGeometricTensorAndConformalVirasoro => .SenseG_QuantumGeometricUncertainty
  | .CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex     => .SenseD_ThermodynamicModularKMS

/-- Secondary semantic sense capturing composite multi-corridor clades (specifically Clade VIII's
Virasoro central charge and Clade V's Cuntz boundary inflow). -/
def secondarySemanticSense : GrandAnomalyTaxonomicClade → GrandAnomalySemanticSense
  | .CladeI_ObliqueIdempotentDefect                       => .SenseA_ProjectorCommutatorObliqueObstruction
  | .CladeII_TopologicalIndexProjectivePoset              => .SenseA_ProjectorCommutatorObliqueObstruction
  | .CladeIII_ConcreteHilbertSewnBoundary                 => .SenseB_TopologicalIndexProjectiveCohomology
  | .CladeIV_SouriauBostConnesModularTransition           => .SenseC_InfiniteHilbertBoundarySewing
  | .CladeV_BulkBoundaryInflowAndGaugeCancellation        => .SenseC_InfiniteHilbertBoundarySewing
  | .CladeVI_GradedLieTKKAndO55TDualityClosure            => .SenseB_TopologicalIndexProjectiveCohomology
  | .CladeVII_PeirceSpineEinsteinCartanFrameDragging      => .SenseA_ProjectorCommutatorObliqueObstruction
  | .CladeVIII_QuantumGeometricTensorAndConformalVirasoro => .SenseH_ConformalCentralCharge
  | .CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex     => .SenseB_TopologicalIndexProjectiveCohomology

/-- **Complete Semantic Coverage Theorem**:
Every one of the eight semantic senses in `GrandAnomalySemanticSense` is realized by the
nine taxonomic clades of `GrandAnomalyTaxonomicClade`. -/
theorem semanticSense_complete_coverage (s : GrandAnomalySemanticSense) :
    ∃ c : GrandAnomalyTaxonomicClade, c.semanticSense = s ∨ c.secondarySemanticSense = s := by
  cases s with
  | SenseA_ProjectorCommutatorObliqueObstruction =>
      exact ⟨.CladeI_ObliqueIdempotentDefect, Or.inl rfl⟩
  | SenseB_TopologicalIndexProjectiveCohomology =>
      exact ⟨.CladeII_TopologicalIndexProjectivePoset, Or.inl rfl⟩
  | SenseC_InfiniteHilbertBoundarySewing =>
      exact ⟨.CladeIII_ConcreteHilbertSewnBoundary, Or.inl rfl⟩
  | SenseD_ThermodynamicModularKMS =>
      exact ⟨.CladeIV_SouriauBostConnesModularTransition, Or.inl rfl⟩
  | SenseE_GradingExtensionHeisenbergCenter =>
      exact ⟨.CladeVI_GradedLieTKKAndO55TDualityClosure, Or.inl rfl⟩
  | SenseF_CurvatureTorsionVielbeinCommutator =>
      exact ⟨.CladeVII_PeirceSpineEinsteinCartanFrameDragging, Or.inl rfl⟩
  | SenseG_QuantumGeometricUncertainty =>
      exact ⟨.CladeVIII_QuantumGeometricTensorAndConformalVirasoro, Or.inl rfl⟩
  | SenseH_ConformalCentralCharge =>
      exact ⟨.CladeVIII_QuantumGeometricTensorAndConformalVirasoro, Or.inr rfl⟩

/-- Multi-level ontology stratum (`M0` → `M3`) of each clade. -/
def metaLevel : GrandAnomalyTaxonomicClade → OntologyMetaLevel
  | .CladeI_ObliqueIdempotentDefect                       => .M1_ProjectorClabject
  | .CladeII_TopologicalIndexProjectivePoset              => .M2_GrassmannianPowertypeOrbit
  | .CladeIII_ConcreteHilbertSewnBoundary                 => .M2_GrassmannianPowertypeOrbit
  | .CladeIV_SouriauBostConnesModularTransition           => .M3_ErlangenCasimirMetaLaw
  | .CladeV_BulkBoundaryInflowAndGaugeCancellation        => .M2_GrassmannianPowertypeOrbit
  | .CladeVI_GradedLieTKKAndO55TDualityClosure            => .M3_ErlangenCasimirMetaLaw
  | .CladeVII_PeirceSpineEinsteinCartanFrameDragging      => .M2_GrassmannianPowertypeOrbit
  | .CladeVIII_QuantumGeometricTensorAndConformalVirasoro => .M2_GrassmannianPowertypeOrbit
  | .CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex     => .M3_ErlangenCasimirMetaLaw

/-- Representation-depth layer of each clade. -/
def repDepth : GrandAnomalyTaxonomicClade → InfoGeometry.Meta.RepDepth
  | .CladeI_ObliqueIdempotentDefect                       => .operator
  | .CladeII_TopologicalIndexProjectivePoset              => .krein
  | .CladeIII_ConcreteHilbertSewnBoundary                 => .transport
  | .CladeIV_SouriauBostConnesModularTransition           => .thermo
  | .CladeV_BulkBoundaryInflowAndGaugeCancellation        => .transport
  | .CladeVI_GradedLieTKKAndO55TDualityClosure            => .krein
  | .CladeVII_PeirceSpineEinsteinCartanFrameDragging      => .operator
  | .CladeVIII_QuantumGeometricTensorAndConformalVirasoro => .operator
  | .CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex     => .thermo

/-- Primary QMS audit bucket of each active clade owner. -/
def qmsBucket : GrandAnomalyTaxonomicClade → AnomalyQMSBucket
  | .CladeI_ObliqueIdempotentDefect                       => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .CladeII_TopologicalIndexProjectivePoset              => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .CladeIII_ConcreteHilbertSewnBoundary                 => .BucketA_GenuineNativeMathlibAnalysis
  | .CladeIV_SouriauBostConnesModularTransition           => .BucketA_GenuineNativeMathlibAnalysis
  | .CladeV_BulkBoundaryInflowAndGaugeCancellation        => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .CladeVI_GradedLieTKKAndO55TDualityClosure            => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .CladeVII_PeirceSpineEinsteinCartanFrameDragging      => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .CladeVIII_QuantumGeometricTensorAndConformalVirasoro => .BucketB_HonestAlgebraicFiniteStageColimitTransport
  | .CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex     => .BucketA_GenuineNativeMathlibAnalysis

/-- All nine clades are verified outside of Bucket C (superseded historical surrogates). -/
theorem active_clade_not_bucketC (c : GrandAnomalyTaxonomicClade) :
    c.qmsBucket ≠ .BucketC_SupersededHistoricalSurrogate := by
  cases c <;> decide

/-- Explicit distinctness of Clade I from all subsequent clades. -/
theorem clades_pairwise_distinct :
    CladeI_ObliqueIdempotentDefect ≠ CladeII_TopologicalIndexProjectivePoset ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeIII_ConcreteHilbertSewnBoundary ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeIV_SouriauBostConnesModularTransition ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeV_BulkBoundaryInflowAndGaugeCancellation ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeVI_GradedLieTKKAndO55TDualityClosure ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeVII_PeirceSpineEinsteinCartanFrameDragging ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeVIII_QuantumGeometricTensorAndConformalVirasoro ∧
    CladeI_ObliqueIdempotentDefect ≠ CladeIX_OmegaAnalyticMomentFoldingAndWittenIndex := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- Universal pairwise distinctness of any two clades with distinct numerical indices. -/
theorem clade_ne_of_index_ne {c₁ c₂ : GrandAnomalyTaxonomicClade} (h : c₁.index ≠ c₂.index) :
    c₁ ≠ c₂ :=
  fun heq => h (heq ▸ rfl)

end GrandAnomalyTaxonomicClade

/-! ## Part III: The Seven Phylogenetic Epochs & Acyclic Causal Poset -/

/-- The seven phylogenetic epochs of anomaly formalization across the repository. -/
inductive GrandAnomalyPhylogeneticEpoch : Type
  | Epoch1_ElementaryObliqueProjector
  | Epoch2_MatrixUnitAndPeirceSpine
  | Epoch3_TopologicalIndexAndProjectiveCocycle
  | Epoch4_EinsteinCartanSpinFrameDragging
  | Epoch5_QuantumGeometricTensorRobertson
  | Epoch6_HigherGradeTDualityAndVirasoroSugawara
  | Epoch7_InfiniteCantorSewingAndKMSModular
  deriving DecidableEq, Repr, Inhabited

namespace GrandAnomalyPhylogeneticEpoch

/-- Chronological causal rank (`0` through `6`) of the phylogenetic epochs. -/
def grandCausalRank : GrandAnomalyPhylogeneticEpoch → ℕ
  | .Epoch1_ElementaryObliqueProjector            => 0
  | .Epoch2_MatrixUnitAndPeirceSpine              => 1
  | .Epoch3_TopologicalIndexAndProjectiveCocycle  => 2
  | .Epoch4_EinsteinCartanSpinFrameDragging       => 3
  | .Epoch5_QuantumGeometricTensorRobertson       => 4
  | .Epoch6_HigherGradeTDualityAndVirasoroSugawara => 5
  | .Epoch7_InfiniteCantorSewingAndKMSModular     => 6

/-- The causal rank function `grandCausalRank` is injective. -/
theorem grandCausalRank_injective : Function.Injective grandCausalRank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder GrandAnomalyPhylogeneticEpoch :=
  LinearOrder.lift' grandCausalRank grandCausalRank_injective

/-- Directed causal dependency edge `u ≺ v` between phylogenetic epochs. -/
inductive GrandCausalEdge : GrandAnomalyPhylogeneticEpoch → GrandAnomalyPhylogeneticEpoch → Prop
  | step {u v : GrandAnomalyPhylogeneticEpoch} (h : u.grandCausalRank < v.grandCausalRank) : GrandCausalEdge u v

/-- Transitive closure of `GrandCausalEdge` strictly increases causal rank. -/
theorem transGen_grandCausalEdge_lt_rank {u v : GrandAnomalyPhylogeneticEpoch}
    (h : Relation.TransGen GrandCausalEdge u v) : u.grandCausalRank < v.grandCausalRank := by
  induction h with
  | single h1 =>
      cases h1 with
      | step hlt => exact hlt
  | tail _ h2 ih =>
      cases h2 with
      | step hlt => exact Nat.lt_trans ih hlt

/-- **Strict Acyclicity Theorem**:
The 7-epoch phylogenetic causal graph is strictly acyclic: no epoch can causally precede itself. -/
theorem grandCausalEdge_acyclic (e : GrandAnomalyPhylogeneticEpoch) :
    ¬ Relation.TransGen GrandCausalEdge e e := by
  intro h
  exact Nat.lt_irrefl e.grandCausalRank (transGen_grandCausalEdge_lt_rank h)

end GrandAnomalyPhylogeneticEpoch

open GrandAnomalyPhylogeneticEpoch

/-! ## Part IV: Cross-Clade Carriers & Master Mathematical Bridges -/

/-- **Universal Ring-Theoretic Oblique Idempotent Perturbation**:
In any associative ring $B$, perturbing an idempotent $P$ ($P^2 = P$) by an upper Peirce corner
$N_+ = P X (1 - P)$ produces an oblique idempotent $P_{\mathrm{obl}} = P + N_+$ whose commutator
with $P$ equals $-N_+$. -/
theorem obliquePerturbation_idem_and_commutator {B : Type*} [Ring B]
    (P X : B) (hP : P * P = P) :
    let Np := P * X * (1 - P)
    let Pobl := P + Np
    Pobl * Pobl = Pobl ∧ Pobl * P - P * Pobl = -Np := by
  dsimp
  have h1P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  set Np := P * X * (1 - P)
  have hPNp : P * Np = Np := by
    dsimp [Np]; calc P * (P * X * (1 - P)) = (P * P) * X * (1 - P) := by noncomm_ring
      _ = P * X * (1 - P) := by rw [hP]
  have hNpP : Np * P = 0 := by
    dsimp [Np]; calc (P * X * (1 - P)) * P = P * X * ((1 - P) * P) := by noncomm_ring
      _ = 0 := by rw [h1P]; noncomm_ring
  have hNpSq : Np * Np = 0 := by
    dsimp [Np]; calc (P * X * (1 - P)) * (P * X * (1 - P))
        = P * X * ((1 - P) * P) * X * (1 - P) := by noncomm_ring
      _ = 0 := by rw [h1P]; noncomm_ring
  constructor
  · calc (P + Np) * (P + Np)
        = P * P + P * Np + Np * P + Np * Np := by noncomm_ring
      _ = P + Np := by rw [hP, hPNp, hNpP, hNpSq]; abel
  · calc (P + Np) * P - P * (P + Np)
        = Np * P - P * Np := by noncomm_ring
      _ = -Np := by rw [hNpP, hPNp]; abel

/-- **Bridge 1 (Oblique Defect to Krein BRST Differential)**:
The matrix unit $E_{01}$ characterizing $[P_{\mathrm{obl}}, P_L] = -E_{01}$ is identically `brstQ2`. -/
theorem grand_bridge_1 :
    GenericObliqueIdempotentAnomaly.E01 (R := ℂ) = brstQ2 ∧
    GenericObliqueIdempotentAnomaly.commutator
        (GenericObliqueIdempotentAnomaly.oblique (R := ℂ))
        GenericObliqueIdempotentAnomaly.leftProjector =
      -brstQ2 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GenericObliqueIdempotentAnomaly.E01, brstQ2, Matrix.single]
  · rw [GenericObliqueIdempotentAnomaly.oblique_commutator_leftProjector]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GenericObliqueIdempotentAnomaly.E01, brstQ2, Matrix.single]

/-- **Bridge 2 (Nilpotent Matrix Commutator Generating Spin Parity Anomaly)**:
For $N = !![0, 1; 0, 0]$ and $N^* = !![0, 0; 1, 0]$, $[N, N^*] = \sigma_z$, $[\sigma_z, N] = 2N$,
and $\{\sigma_z, N\} = 0$. -/
theorem grand_bridge_2 :
    let N : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    let N_star : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
    N * N_star - N_star * N = pauliZ2 ∧
    pauliZ2 * N = N ∧
    pauliZ2 * N_star = -N_star ∧
    pauliZ2 * N - N * pauliZ2 = (2 : ℂ) • N ∧
    pauliZ2 * N + N * pauliZ2 = 0 := by
  dsimp [pauliZ2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring }

theorem grand_bridge_2_commutator :
    pauliZ2 * !![0, (1 : ℂ); 0, 0] - !![0, (1 : ℂ); 0, 0] * pauliZ2 =
      (2 : ℂ) • !![0, (1 : ℂ); 0, 0] :=
  grand_bridge_2.2.2.2.1

/-- **Bridge 3 (Drazin-Moore-Penrose Projection Mismatch to Off-Diagonal Nilpotent Peirce Corner)**:
The upper homotope bracket is localized in $P B (1-P)$ and squares to zero. -/
theorem grand_bridge_3 {B : Type*} [Ring B] {P : B} (hP : P * P = P) (C A Z : B) :
    P * InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z =
      InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z * (1 - P) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z *
      InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z = 0 :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket_corner_and_square_zero hP C A Z

/-- **General $n \times n$ Graded Supertrace Doubling & Algebraic McKean-Singer Vanishing**:
Over any commutative ring $R$ and finite index type $n$, for any grading matrix $\Gamma$ and odd
operator $A$ ($\Gamma A = -A \Gamma$):
1. $\operatorname{Tr}([A, B]) = 0$ for all $B$.
2. $\operatorname{Tr}(\Gamma (A B + B A)) = 0$ for all $B$ (supertrace vanishes on odd anticommutators).
3. $\operatorname{Tr}(\Gamma (A B - B A)) = 2 \operatorname{Tr}(\Gamma (A B))$ (supertrace doubles on odd commutators).
4. $2 \operatorname{Tr}(\Gamma A^{2(k+1)}) = 0$ for all $k : \mathbb{N}$ (McKean-Singer even-power vanishing). -/
theorem general_superTrace_odd_commutator_and_even_pow
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (Γ A B : Matrix n n R) (hOdd : Γ * A = -(A * Γ)) (k : ℕ) :
    Matrix.trace (A * B - B * A) = 0 ∧
    Matrix.trace (Γ * (A * B + B * A)) = 0 ∧
    Matrix.trace (Γ * (A * B - B * A)) = 2 * Matrix.trace (Γ * (A * B)) ∧
    2 * Matrix.trace (Γ * (A ^ (2 * (k + 1)))) = 0 := by
  have hFlip : ∀ X : Matrix n n R, Matrix.trace (Γ * (X * A)) = -Matrix.trace (Γ * (A * X)) := by
    intro X
    calc Matrix.trace (Γ * (X * A))
        = Matrix.trace ((Γ * X) * A) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (A * (Γ * X)) := Matrix.trace_mul_comm (Γ * X) A
      _ = Matrix.trace ((A * Γ) * X) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (-(Γ * A) * X) := by rw [hOdd, neg_neg]
      _ = -Matrix.trace ((Γ * A) * X) := by rw [Matrix.neg_mul, Matrix.trace_neg]
      _ = -Matrix.trace (Γ * (A * X)) := by rw [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  · rw [Matrix.mul_add, Matrix.trace_add, hFlip B, add_neg_cancel]
  · rw [Matrix.mul_sub, Matrix.trace_sub, hFlip B]
    ring
  · have hPow : A ^ (2 * (k + 1)) = A * A ^ (2 * k + 1) ∧
                A ^ (2 * (k + 1)) = A ^ (2 * k + 1) * A := by
      have heq : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [heq]
      exact ⟨pow_succ' A (2 * k + 1), pow_succ A (2 * k + 1)⟩
    have hAnti : Matrix.trace (Γ * (A * A ^ (2 * k + 1) + A ^ (2 * k + 1) * A)) = 0 := by
      rw [Matrix.mul_add, Matrix.trace_add, hFlip (A ^ (2 * k + 1)), add_neg_cancel]
    rw [← hPow.1, ← hPow.2] at hAnti
    rw [Matrix.mul_add, Matrix.trace_add] at hAnti
    calc 2 * Matrix.trace (Γ * A ^ (2 * (k + 1)))
        = Matrix.trace (Γ * A ^ (2 * (k + 1))) + Matrix.trace (Γ * A ^ (2 * (k + 1))) := two_mul _
      _ = 0 := hAnti

/-- **Bridge 4 (Socratic Aporia I Resolution: Ungraded Tracial Vanishing vs Graded Supertrace Doubling)**: -/
theorem grand_bridge_4 (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA0 : A 0 0 = 0) (hA1 : A 1 1 = 0)
    (hB0 : B 0 0 = 0) (hB1 : B 1 1 = 0) :
    Matrix.trace (A * B - B * A) = 0 ∧
    Matrix.trace (pauliZ2 * (A * B - B * A)) = 2 * Matrix.trace (pauliZ2 * (A * B)) := by
  constructor
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  · dsimp [Matrix.trace, pauliZ2, Fin.sum_univ_two]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hA0, hA1, hB0, hB1]
    ring

/-- **Anomalous Bianchi Identity in Green-Schwarz Descent**:
For any exterior differential $d : \Omega^3 \to+ \Omega^4$ with $d(dB) = 0$ and Chern-Simons
transgression $d\Omega_{\mathrm{CS}} = \operatorname{tr}(F \wedge F)$, the gauge-invariant 3-form
$H = dB - \Omega_{\mathrm{CS}}$ obeys $dH = -\operatorname{tr}(F \wedge F)$. -/
theorem green_schwarz_bianchi_defect
    {Forms3 Forms4 : Type*} [AddCommGroup Forms3] [AddCommGroup Forms4]
    (d3 : Forms3 →+ Forms4) (dB omegaCS : Forms3) (trFF : Forms4)
    (hd2 : d3 dB = 0) (hTrans : d3 omegaCS = trFF) :
    d3 (dB - omegaCS) = -trFF := by
  rw [map_sub, hd2, hTrans, zero_sub]

/-- **Bridge 5 (Bulk Chern-Simons Inflow to Green-Schwarz Modified 3-Form Gauge Invariance)**: -/
theorem grand_bridge_5
    {R : Type*} [Ring R] [StarRing R]
    (sys : Cuntz2System R)
    {M : Type*} [AddCommGroup M]
    (tr : CyclicTrace R M)
    (D X : R)
    {Forms : Type*} [AddCommGroup Forms]
    (dB omegaCS delta_dB delta_omegaCS : Forms)
    (h_inflow : delta_dB = delta_omegaCS) :
    totalGreenSchwarzAnomaly sys tr D X = 0 ∧
    (dB + delta_dB) - (omegaCS + delta_omegaCS) = dB - omegaCS :=
  ⟨green_schwarz_inflow_cancellation sys tr D X,
   green_schwarz_H_gauge_invariant dB omegaCS delta_dB delta_omegaCS h_inflow⟩

/-- **Bridge 5B (Cuntz Chiral Supercharges, Kugo-Ojima Exactness, and Cantor Branch Chirality)**:
Wires `ChiralCuntzSuperchargeBridge`, `ChiralCuntzAnomalyPartitionBridge`, and Cantor boundary
trace preservation from `GreenSchwarzAnomalyInflowBridge`:
$Q_+^2 = Q_-^2 = 0$, $\{Q_+, Q_-\} = 1$, $\Gamma^2 = 1$, Kugo-Ojima exactness, exact supertrace
and quantum-anomaly annihilation on BRST-exact observables, and vanishing normalized Cantor
branch-chirality trace at every stage $n$. -/
theorem cuntz_supercharge_and_exact_inflow_bridge
    {R : Type*} [Ring R] [StarRing R]
    (sys : Cuntz2System R)
    {M : Type*} [AddCommGroup M]
    (tr : CyclicTrace R M)
    (D y : R)
    (hD_comm : D * Q_plus sys = Q_plus sys * D)
    (n : ℕ) :
    Q_plus sys * Q_plus sys = 0 ∧
    Q_minus sys * Q_minus sys = 0 ∧
    Q_plus sys * Q_minus sys + Q_minus sys * Q_plus sys = 1 ∧
    chirality sys * chirality sys = 1 ∧
    (∀ x : R, Q_plus sys * x = 0 → x = Q_plus sys * (Q_minus sys * x)) ∧
    supertrace sys tr (Q_plus sys * y + y * Q_plus sys) = 0 ∧
    quantumAnomaly sys tr D (Q_plus sys * y + y * Q_plus sys) = 0 ∧
    branchChirality n * branchChirality n = 1 ∧
    InfoGeometry.Canonical.KMSTraceColimit.normalizedTrace (n + 1) (branchChirality n) = 0 :=
  ⟨Q_plus_sq_zero sys,
   Q_minus_sq_zero sys,
   chiral_susy_anticommutator_eq_one sys,
   chirality_sq sys,
   kugo_ojima_exactness sys,
   supertrace_exact_annihilation sys tr y,
   quantumAnomaly_vanishes_exact sys tr D y hD_comm,
   branchChirality_sq n,
   normalizedTrace_branchChirality n⟩

/-! ### Clade II / VI De-Conflation: Real $\mathrm{Pin}^{\pm}$ Spinors & Analytic $\mu_{16}$ Witten Phase -/

/-- Real $\mathrm{Pin}^-$ reflection generator $\gamma_- = \sigma_x$ satisfying $\gamma_-^2 = +I_2$. -/
def pinMinusGen : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Real $\mathrm{Pin}^+$ complex structure $\gamma_+ = i\sigma_y$ satisfying $\gamma_+^2 = -I_2$. -/
def pinPlusGen : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Chiral spinor volume element $\Gamma = \gamma_- \gamma_+ = -\sigma_z$ on $\mathbb{R}^2$. -/
def pinChiralGrading : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

/-- **Pin± Clifford Reflection & Chirality Inversion Theorem**:
$\gamma_-^2 = +1$, $\gamma_+^2 = -1$, $\{\gamma_-, \gamma_+\} = 0$, $\Gamma = \gamma_- \gamma_+$ satisfies
$\Gamma^2 = +1$, and reflection inverts chirality ($\gamma_- \Gamma \gamma_- = -\Gamma$). -/
theorem pin_clifford_reflection_parity_anomaly :
    pinMinusGen * pinMinusGen = 1 ∧
    pinPlusGen * pinPlusGen = -1 ∧
    pinMinusGen * pinPlusGen = pinChiralGrading ∧
    pinMinusGen * pinPlusGen + pinPlusGen * pinMinusGen = 0 ∧
    pinChiralGrading * pinChiralGrading = 1 ∧
    pinMinusGen * pinChiralGrading * pinMinusGen = -pinChiralGrading := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pinMinusGen, pinPlusGen, pinChiralGrading, Matrix.mul_apply, Fin.sum_univ_two] }

/-- **Witten $\mathbb{Z}_{16}$ Analytic $\eta$-Invariant Phase Theorem**:
The Majorana-Weyl reflection partition phase $\exp(2\pi i \nu / 16)$ equals $1 \in \mathbb{C}$
if and only if $(\nu : \mathrm{ZMod}\;16) = 0$. -/
theorem witten_eta_phase_trivial_iff_mod16 (ν : ℤ) :
    Complex.exp ((ν : ℂ) * (2 * ↑Real.pi * Complex.I) / 16) = 1 ↔ (ν : ZMod 16) = 0 := by
  rw [Complex.exp_eq_one_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h16 : (16 : ℂ) ≠ 0 := by norm_num
    have hn' := (div_eq_iff h16).mp hn
    have hmul : (ν : ℂ) * (2 * ↑Real.pi * Complex.I) =
        ((16 * n : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast
      calc (ν : ℂ) * (2 * ↑Real.pi * Complex.I)
          = (n : ℂ) * (2 * ↑Real.pi * Complex.I) * 16 := hn'
        _ = 16 * (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by ring
    exact Int.cast_injective (mul_right_cancel₀ Complex.two_pi_I_ne_zero hmul)
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

/-- **Bridge 6 ($\mathrm{Pin}^{\pm}$ Owners, Chirality Inversion, & Witten $\mathbb{Z}_{16}$ Anomaly Cancellation)**:
Wires `WittenParityAnomalyBridge.AnomalyFree`, `modular_j_is_pin_minus`, and `complex_i_is_pin_plus`
directly to the analytic $\eta$-invariant phase law and real $\mathrm{Cl}(1,1)$ chirality inversion. -/
theorem grand_bridge_6 (nu : ℕ) :
    (WittenParityAnomalyBridge.AnomalyFree nu ↔ (nu : ZMod 16) = 0) ∧
    (Complex.exp (((nu : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) / 16) = 1 ↔ (nu : ZMod 16) = 0) ∧
    WittenParityAnomalyBridge.IsPinMinus
      (InfoGeometry.Krein.modular_j (E := ℝ)) ∧
    WittenParityAnomalyBridge.IsPinPlus
      (InfoGeometry.Krein.complex_i (E := ℝ)) ∧
    (pinMinusGen * pinMinusGen = 1 ∧
     pinPlusGen * pinPlusGen = -1 ∧
     pinMinusGen * pinChiralGrading * pinMinusGen = -pinChiralGrading) := by
  have hPin := pin_clifford_reflection_parity_anomaly
  refine ⟨?_, ?_,
    WittenParityAnomalyBridge.modular_j_is_pin_minus (E := ℝ),
    WittenParityAnomalyBridge.complex_i_is_pin_plus (E := ℝ),
    ⟨hPin.1, hPin.2.1, hPin.2.2.2.2.2⟩⟩
  · unfold WittenParityAnomalyBridge.AnomalyFree
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_iff_mod_eq_zero.symm
  · simpa using witten_eta_phase_trivial_iff_mod16 (nu : ℤ)

/-! ### Clade VI / IX De-Conflation: Bivector vs. 3-Associator Rank Law & $10 \times 10$ $\mathfrak{so}(5,5)$ -/


private lemma choose_three_gt_add_five (n : ℕ) : n + 5 < Nat.choose (n + 5) 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hc2 : n + 4 ≤ Nat.choose (n + 5) 2 := by
        rw [show n + 5 = (n + 4) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
        omega
      have hc3 : Nat.choose (n + 1 + 5) 3 = Nat.choose (n + 5) 2 + Nat.choose (n + 5) 3 := by
        rw [show n + 1 + 5 = (n + 5) + 1 by omega]
        exact Nat.choose_succ_succ (n + 5) 2
      omega

/-- **Torsional Bivector vs. Alternating 3-Associator Dimensional Disambiguation**:
Resolves the superposition in Clade VI / VII / IX:
1. Skew-symmetric torsional 2-forms ($\binom{r}{2}$) match vector rank $r > 0$ uniquely at $r = 3$
   ($\binom{3}{2} = 3$, 3D cross-product / Hodge self-duality).
2. Skew-symmetric 2-forms ($\binom{r}{2}$) match alternating 3-associators ($\binom{r}{3}$) for $r \ge 3$
   uniquely at $r = 5$ ($\binom{5}{2} = \binom{5}{3} = 10$, 5D Hodge duality inside $\mathfrak{so}(5,5)$). -/
theorem torsion_bivector_vs_associator_disambiguation :
    (∀ r : ℕ, 0 < r → (Nat.choose r 2 = r ↔ r = 3)) ∧
    (∀ r : ℕ, 3 ≤ r → (Nat.choose r 2 = Nat.choose r 3 ↔ r = 5)) := by
  constructor
  · intro r hr
    match r with
    | 0 => omega
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | n + 4 =>
        have h1 : Nat.choose (n + 4) 2 = (n + 3) + Nat.choose (n + 3) 2 := by
          rw [show n + 4 = (n + 3) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
        have h2 : Nat.choose (n + 3) 2 = (n + 2) + Nat.choose (n + 2) 2 := by
          rw [show n + 3 = (n + 2) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
        omega
  · intro r hr
    match r with
    | 0 | 1 | 2 => omega
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | n + 6 =>
        have h2 : Nat.choose (n + 6) 2 = (n + 5) + Nat.choose (n + 5) 2 := by
          rw [show n + 6 = (n + 5) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
        have h3 : Nat.choose (n + 6) 3 = Nat.choose (n + 5) 2 + Nat.choose (n + 5) 3 := by
          rw [show n + 6 = (n + 5) + 1 by omega, Nat.choose_succ_succ]
        have hgt := choose_three_gt_add_five n
        omega

/-- **Bridge 7 (Connected Anomaly Quadratic Bivector Law & Critical Rank Bridge)**:
Bridges `Omega.CircleDimension.paper_cdim_anomaly_quadratic_law` to `torsion_bivector_vs_associator_disambiguation`
across arbitrary discrete torsion rank `t`. -/
theorem grand_bridge_7 (r t : ℕ) :
    Omega.CircleDimension.anomalyConnectedDim r t = Nat.choose r 2 ∧
    (0 < r → (Omega.CircleDimension.anomalyConnectedDim r t = r ↔ r = 3)) ∧
    (3 ≤ r → (Omega.CircleDimension.anomalyConnectedDim r t = Nat.choose r 3 ↔ r = 5)) := by
  have hQuad : Omega.CircleDimension.anomalyConnectedDim r t = Nat.choose r 2 :=
    (Omega.CircleDimension.paper_cdim_anomaly_quadratic_law r t).2.1
  refine ⟨hQuad, fun hr => ?_, fun hr3 => ?_⟩
  · rw [hQuad]
    exact torsion_bivector_vs_associator_disambiguation.1 r hr
  · rw [hQuad]
    exact torsion_bivector_vs_associator_disambiguation.2 r hr3

/-- **Bridge 8 ($2 \times 2$ Contact $\mathfrak{sl}_2$ Core of T-Duality)**: -/
theorem grand_bridge_8 :
    let Z_plus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let Z_minus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let T : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let euler : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    T * T = 1 ∧
    T * Z_plus * T = Z_minus ∧
    T * Z_minus * T = Z_plus ∧
    Z_plus * Z_minus - Z_minus * Z_plus = euler ∧
    T * euler * T = -euler := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }

/-- First grade-$+1$ TKK generator $E_{01}$ on $\mathbb{R}^3$ (top-level T16 witness for `('3', '3', 'ℝ')`). -/
def tkkPlus1A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- Second grade-$+1$ TKK generator $E_{12}$ on $\mathbb{R}^3$ (top-level T16 witness for `('3', '3', 'ℝ')`). -/
def tkkPlus1B : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 1; 0, 0, 0]

/-- Explicit non-commutativity witness for real $3 \times 3$ matrices (`('3', '3', 'ℝ')`). -/
theorem tkkPlus1A_tkkPlus1B_not_commute : tkkPlus1A * tkkPlus1B ≠ tkkPlus1B * tkkPlus1A := by
  intro h
  have hentry := congrFun (congrFun h 0) 2
  simp only [tkkPlus1A, tkkPlus1B, Matrix.mul_apply, Fin.sum_univ_three] at hentry
  norm_num at hentry

/-- Elementary matrix unit $c \cdot E_{i,j}$ on an arbitrary decidable index type. -/
def eMat {n R : Type*} [DecidableEq n] [Zero R] (i j : n) (c : R) : Matrix n n R :=
  Matrix.of fun r s => if r = i ∧ s = j then c else 0

@[simp]
lemma eMat_mul_eMat {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (i j k l : n) (a b : R) :
    eMat i j a * eMat k l b = if j = k then eMat i l (a * b) else 0 := by
  ext r s
  simp only [eMat, Matrix.mul_apply, Matrix.of_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte]
    rw [Fintype.sum_eq_single j]
    · by_cases hri : r = i <;> by_cases hsl : s = l <;> simp [hri, hsl]
    · intro x hx
      by_cases hri : r = i <;> simp [hri, hx]
  · simp only [hjk, ↓reduceIte, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxj : x = j
    · subst hxj; simp [hjk]
    · simp [hxj]

@[simp]
lemma eMat_transpose {n R : Type*} [DecidableEq n] [Zero R] (i j : n) (c : R) :
    (eMat i j c)ᵀ = eMat j i c := by
  ext r s
  simp [eMat, Matrix.transpose_apply, and_comm]

/-- Isotropic sheet swap on `Fin 5 ⊕ Fin 5` exchanging coordinates `inl i` and dual momenta `inr i`. -/
def swapIdx : Fin 5 ⊕ Fin 5 → Fin 5 ⊕ Fin 5
  | .inl i => .inr i
  | .inr i => .inl i

@[simp]
lemma swapIdx_swapIdx (u : Fin 5 ⊕ Fin 5) : swapIdx (swapIdx u) = u := by
  cases u <;> rfl

/-- Split-signature $O(5,5)$ metric $\eta_{5,5} = \left(\begin{smallmatrix} 0 & I_5 \\ I_5 & 0 \end{smallmatrix}\right)$
on `Fin 5 ⊕ Fin 5`, simultaneously serving as the global Buscher $O(5,5)$ T-duality involution. -/
def so55Metric : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ :=
  Matrix.of fun u v => if v = swapIdx u then 1 else 0

/-- Membership predicate for the 45-dimensional split-orthogonal Lie algebra $\mathfrak{so}(5,5)$. -/
def inSo55 (X : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ) : Prop :=
  Xᵀ * so55Metric + so55Metric * X = 0

lemma so55Metric_transpose : so55Metricᵀ = so55Metric := by
  ext u v
  simp only [so55Metric, Matrix.transpose_apply, Matrix.of_apply]
  cases u <;> cases v <;> simp [swapIdx, eq_comm]

lemma so55Metric_sq : so55Metric * so55Metric = 1 := by
  ext u v
  simp only [so55Metric, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_eq_single (swapIdx u)]
  · by_cases huv : v = u
    · subst huv; simp
    · have hne : u ≠ v := Ne.symm huv
      simp [huv, hne]
  · intro x hx
    simp [hx]

@[simp]
lemma so55Metric_mul_eMat (u v : Fin 5 ⊕ Fin 5) (c : ℝ) :
    so55Metric * eMat u v c = eMat (swapIdx u) v c := by
  ext r s
  simp only [so55Metric, eMat, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.sum_eq_single (swapIdx r)]
  · have hiff : swapIdx r = u ↔ r = swapIdx u :=
      ⟨fun h => by rw [← h, swapIdx_swapIdx], fun h => by rw [h, swapIdx_swapIdx]⟩
    by_cases hru : r = swapIdx u <;> by_cases hsv : s = v <;> simp [hiff, hru, hsv]
  · intro x hx
    simp [hx]

@[simp]
lemma eMat_mul_so55Metric (u v : Fin 5 ⊕ Fin 5) (c : ℝ) :
    eMat u v c * so55Metric = eMat u (swapIdx v) c := by
  ext r s
  simp only [so55Metric, eMat, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.sum_eq_single v]
  · by_cases hru : r = u <;> by_cases hsv : s = swapIdx v <;> simp [hru, hsv]
  · intro x hx
    by_cases hru : r = u <;> simp [hru, hx]

/-- Lie bracket closure of $\mathfrak{so}(5,5)$: if $X, Y \in \mathfrak{so}(5,5)$, then $[X, Y] \in \mathfrak{so}(5,5)$. -/
theorem so55_lie_closed {X Y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ}
    (hX : inSo55 X) (hY : inSo55 Y) : inSo55 (X * Y - Y * X) := by
  unfold inSo55 at *
  have hXt : Xᵀ * so55Metric = -(so55Metric * X) := eq_neg_of_add_eq_zero_left hX
  have hYt : Yᵀ * so55Metric = -(so55Metric * Y) := eq_neg_of_add_eq_zero_left hY
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (Yᵀ * Xᵀ - Xᵀ * Yᵀ) * so55Metric + so55Metric * (X * Y - Y * X)
      = Yᵀ * (Xᵀ * so55Metric) - Xᵀ * (Yᵀ * so55Metric) +
          so55Metric * X * Y - so55Metric * Y * X := by noncomm_ring
    _ = Yᵀ * (-(so55Metric * X)) - Xᵀ * (-(so55Metric * Y)) +
          so55Metric * X * Y - so55Metric * Y * X := by rw [hXt, hYt]
    _ = -(Yᵀ * so55Metric) * X + (Xᵀ * so55Metric) * Y +
          so55Metric * X * Y - so55Metric * Y * X := by noncomm_ring
    _ = -(-(so55Metric * Y)) * X + (-(so55Metric * X)) * Y +
          so55Metric * X * Y - so55Metric * Y * X := by rw [hXt, hYt]
    _ = 0 := by noncomm_ring

/-- Canonical $\mathfrak{so}(5,5)$ bivector wedge generator $W(u, v) = E_{u, \mathrm{swap}(v)} - E_{v, \mathrm{swap}(u)}$. -/
def so55Wedge (u v : Fin 5 ⊕ Fin 5) : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ :=
  eMat u (swapIdx v) 1 - eMat v (swapIdx u) 1

lemma so55Wedge_inSo55 (u v : Fin 5 ⊕ Fin 5) : inSo55 (so55Wedge u v) := by
  unfold inSo55 so55Wedge
  simp only [Matrix.transpose_sub, eMat_transpose, Matrix.sub_mul, Matrix.mul_sub,
    eMat_mul_so55Metric, so55Metric_mul_eMat]
  abel

/-- Grade-$+2$ Heisenberg anomaly center $Z_{+2} = W(x_0, x_1) \in \mathfrak{so}(5,5)$. -/
def so55CenterPlus2 : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ := so55Wedge (.inl 0) (.inl 1)

/-- Grade-$-2$ Heisenberg anomaly center $Z_{-2} = W(p_0, p_1) \in \mathfrak{so}(5,5)$. -/
def so55CenterMinus2 : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ := so55Wedge (.inr 0) (.inr 1)

/-- Contact Euler grading element $H_{\mathrm{contact}} = W(x_0, p_0) + W(x_1, p_1) \in \mathfrak{so}(5,5)$. -/
def so55ContactEuler : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ :=
  so55Wedge (.inl 0) (.inr 0) + so55Wedge (.inl 1) (.inr 1)

/-- Grade-$+1$ TKK Heisenberg momentum generator $P_{+1} = W(x_0, x_2) \in \mathfrak{so}(5,5)$. -/
def so55Grade1P : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ := so55Wedge (.inl 0) (.inl 2)

/-- Grade-$+1$ TKK Heisenberg position generator $Q_{+1} = W(p_2, x_1) \in \mathfrak{so}(5,5)$. -/
def so55Grade1Q : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ := so55Wedge (.inr 2) (.inl 1)

/-- Explicit non-commutativity witness for `Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ`. -/
theorem so55Grade1P_so55Grade1Q_not_commute :
    so55Grade1P * so55Grade1Q ≠ so55Grade1Q * so55Grade1P := by
  intro h
  have hdiff : so55Grade1P * so55Grade1Q - so55Grade1Q * so55Grade1P = 0 := sub_eq_zero.mpr h
  have hbracket : so55Grade1P * so55Grade1Q - so55Grade1Q * so55Grade1P = so55CenterPlus2 := by
    simp [so55Grade1P, so55Grade1Q, so55CenterPlus2, so55Wedge, swapIdx,
      Matrix.sub_mul, Matrix.mul_sub, eMat_mul_eMat]
  rw [hbracket] at hdiff
  have h01 := congrFun (congrFun hdiff (.inl 0)) (.inr 1)
  simp [so55CenterPlus2, so55Wedge, eMat, swapIdx] at h01

/-- **Bridge 8B (Genuine $10 \times 10$ $\mathfrak{so}(5,5)$ 5-Graded Contact Heisenberg, $O(5,5)$ T-Duality,
Conformal Grade-$\pm 2$ Closure, and $\mathrm{Cl}(5,5)$ Bott Periodicity)**:
1. $Z_{\pm 2}, H_{\mathrm{contact}}, P_{+1}, Q_{+1} \in \mathfrak{so}(5,5)$ with $Z_{+2} \ne 0$.
2. Grade-$+1$ TKK bracket $[P_{+1}, Q_{+1}] = Z_{+2}$ generates the grade-$+2$ Heisenberg center.
3. Exact 5-grading eigenvalues: $[H_{\mathrm{contact}}, Z_{\pm 2}] = \pm 2 Z_{\pm 2}$ and $[H_{\mathrm{contact}}, P_{+1}] = P_{+1}$.
4. Contact closure $[Z_{-2}, Z_{+2}] = H_{\mathrm{contact}}$.
5. $O(5,5)$ Buscher T-duality $T = \eta_{5,5}$ preserves $\eta_{5,5}$, exchanges $T Z_{\pm 2} T = Z_{\mp 2}$,
   and inverts $T H_{\mathrm{contact}} T = -H_{\mathrm{contact}}$.
6. Directly connects to the conformal 5-grade closure owners (`O55FiveGradeClosure.u5_u4_commutator_grade_pos_two`,
   `v5_v4_commutator_grade_neg_two`) and $\mathrm{Cl}(5,5)$ Bott periodicity (`O55BottAnomalyClosure.cl55_bott_anomaly_closure_achieved_eq_owner`). -/
theorem grand_bridge_8_so55_five_grading :
    inSo55 so55CenterPlus2 ∧
    inSo55 so55CenterMinus2 ∧
    inSo55 so55ContactEuler ∧
    inSo55 so55Grade1P ∧
    inSo55 so55Grade1Q ∧
    so55CenterPlus2 ≠ 0 ∧
    (so55Grade1P * so55Grade1Q - so55Grade1Q * so55Grade1P = so55CenterPlus2) ∧
    (so55ContactEuler * so55CenterPlus2 - so55CenterPlus2 * so55ContactEuler =
      (2 : ℝ) • so55CenterPlus2) ∧
    (so55ContactEuler * so55Grade1P - so55Grade1P * so55ContactEuler = so55Grade1P) ∧
    (so55ContactEuler * so55CenterMinus2 - so55CenterMinus2 * so55ContactEuler =
      (-2 : ℝ) • so55CenterMinus2) ∧
    (so55CenterMinus2 * so55CenterPlus2 - so55CenterPlus2 * so55CenterMinus2 = so55ContactEuler) ∧
    (so55Metricᵀ * so55Metric * so55Metric = so55Metric) ∧
    (so55Metric * so55CenterPlus2 * so55Metric = so55CenterMinus2) ∧
    (so55Metric * so55CenterMinus2 * so55Metric = so55CenterPlus2) ∧
    (so55Metric * so55ContactEuler * so55Metric = -so55ContactEuler) ∧
    (InfoGeometry.Clifford.ConformalLieAlgebra55.u5 * InfoGeometry.Clifford.ConformalLieAlgebra55.u4 -
      InfoGeometry.Clifford.ConformalLieAlgebra55.u4 * InfoGeometry.Clifford.ConformalLieAlgebra55.u5 ∈
        InfoGeometry.Clifford.ConformalLieAlgebra55.gradeSpace
          InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.posTwo) ∧
    (InfoGeometry.Clifford.ConformalLieAlgebra55.v5 * InfoGeometry.Clifford.ConformalLieAlgebra55.v4 -
      InfoGeometry.Clifford.ConformalLieAlgebra55.v4 * InfoGeometry.Clifford.ConformalLieAlgebra55.v5 ∈
        InfoGeometry.Clifford.ConformalLieAlgebra55.gradeSpace
          InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.negTwo) ∧
    (O55BottAnomalyClosure.cl55_bott_anomaly_closure_achieved =
      SplitCliffordTensorBridge.splitCliffordTensorStepEquiv 4) := by
  have hEulerIn : inSo55 so55ContactEuler := by
    unfold inSo55 so55ContactEuler
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    have h0 := so55Wedge_inSo55 (.inl 0) (.inr 0)
    have h1 := so55Wedge_inSo55 (.inl 1) (.inr 1)
    unfold inSo55 at h0 h1
    calc (so55Wedge (.inl 0) (.inr 0))ᵀ * so55Metric + (so55Wedge (.inl 1) (.inr 1))ᵀ * so55Metric +
          (so55Metric * so55Wedge (.inl 0) (.inr 0) + so55Metric * so55Wedge (.inl 1) (.inr 1))
        = ((so55Wedge (.inl 0) (.inr 0))ᵀ * so55Metric + so55Metric * so55Wedge (.inl 0) (.inr 0)) +
          ((so55Wedge (.inl 1) (.inr 1))ᵀ * so55Metric + so55Metric * so55Wedge (.inl 1) (.inr 1)) := by abel
      _ = 0 := by rw [h0, h1, add_zero]
  refine ⟨so55Wedge_inSo55 _ _, so55Wedge_inSo55 _ _, hEulerIn,
          so55Wedge_inSo55 _ _, so55Wedge_inSo55 _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          O55FiveGradeClosure.u5_u4_commutator_grade_pos_two,
          O55FiveGradeClosure.v5_v4_commutator_grade_neg_two,
          O55BottAnomalyClosure.cl55_bott_anomaly_closure_achieved_eq_owner⟩
  · intro h
    have h01 := congrFun (congrFun h (.inl 0)) (.inr 1)
    simp [so55CenterPlus2, so55Wedge, eMat, swapIdx] at h01
  · simp [so55Grade1P, so55Grade1Q, so55CenterPlus2, so55Wedge, swapIdx,
      Matrix.sub_mul, Matrix.mul_sub, eMat_mul_eMat]
  · rw [show (2 : ℝ) • so55CenterPlus2 = so55CenterPlus2 + so55CenterPlus2 by
          rw [← one_add_one_eq_two, add_smul, one_smul]]
    simp [so55ContactEuler, so55CenterPlus2, so55Wedge, swapIdx,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, eMat_mul_eMat]
    abel
  · simp [so55ContactEuler, so55Grade1P, so55Wedge, swapIdx,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, eMat_mul_eMat]
  · rw [show (-2 : ℝ) • so55CenterMinus2 = -(so55CenterMinus2 + so55CenterMinus2) by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul, ← one_add_one_eq_two, add_smul, one_smul]]
    simp [so55ContactEuler, so55CenterMinus2, so55Wedge, swapIdx,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, eMat_mul_eMat]
    abel
  · simp [so55CenterMinus2, so55CenterPlus2, so55ContactEuler, so55Wedge, swapIdx,
      Matrix.sub_mul, Matrix.mul_sub, eMat_mul_eMat]
    abel
  · rw [so55Metric_transpose, so55Metric_sq, Matrix.one_mul]
  · simp [so55CenterPlus2, so55CenterMinus2, so55Wedge, swapIdx, Matrix.mul_sub, Matrix.sub_mul]
  · simp [so55CenterMinus2, so55CenterPlus2, so55Wedge, swapIdx, Matrix.mul_sub, Matrix.sub_mul]
  · simp [so55ContactEuler, so55Wedge, swapIdx,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
    abel

/-! ### Clade VII Completion: Deformed $\mathrm{Cl}(1,1)$ Peirce Spine & Kantor-Jordan Associator -/

/-- Unnormalized symmetrized Jordan product $a \bullet b = a b + b a$. -/
def jordanMul {B : Type*} [Ring B] (a b : B) : B := a * b + b * a

/-- Jordan associator $\mathcal{A}_\bullet(a, b, c) = (a \bullet b) \bullet c - a \bullet (b \bullet c)$. -/
def jordanAssociator {B : Type*} [Ring B] (a b c : B) : B :=
  jordanMul (jordanMul a b) c - jordanMul a (jordanMul b c)

/-- Peirce idempotency curvature defect $\delta(V) = V^2 - V$. -/
def peirceCurvatureDefect {B : Type*} [Ring B] (V : B) : B := V * V - V

lemma peirce_chiral_einstein_anomaly {B : Type*} [Ring B]
    (P X Y : B) (hP : P * P = P) :
    let Np := P * X * (1 - P)
    let Nm := (1 - P) * Y * P
    let Phi := Np + Nm
    let J := Np - Nm
    let V := Np * Nm + Nm * Np
    let S_P := 2 * P - 1
    S_P * (Phi * J - J * Phi) = -2 * V := by
  dsimp
  open InfoGeometry.OperatorAlgebra.PeirceSpine in
  rw [show (2 : B) * P - 1 = invS P by dsimp [invS]; noncomm_ring,
      show (-2 : B) * (P * X * (1 - P) * ((1 - P) * Y * P) + (1 - P) * Y * P * (P * X * (1 - P))) =
        -((2 : ℤ) • (P * X * (1 - P) * ((1 - P) * Y * P) + (1 - P) * Y * P * (P * X * (1 - P)))) by noncomm_ring]
  open InfoGeometry.OperatorAlgebra.PeirceSpine in
  peirce_nf hP

lemma peirce_spin_frame_dragging {B : Type*} [Ring B]
    (P X Y : B) (hP : P * P = P) :
    let Np := P * X * (1 - P)
    let Nm := (1 - P) * Y * P
    let Phi := Np + Nm
    let J := Np - Nm
    let Sigma := Np * Nm - Nm * Np
    let V := Np * Nm + Nm * Np
    Sigma * Phi - Phi * Sigma = 2 * (V * J) := by
  dsimp
  rw [show (2 : B) * ((P * X * (1 - P) * ((1 - P) * Y * P) + (1 - P) * Y * P * (P * X * (1 - P))) *
        (P * X * (1 - P) - (1 - P) * Y * P)) =
        (2 : ℤ) • ((P * X * (1 - P) * ((1 - P) * Y * P) + (1 - P) * Y * P * (P * X * (1 - P))) *
        (P * X * (1 - P) - (1 - P) * Y * P)) by noncomm_ring]
  open InfoGeometry.OperatorAlgebra.PeirceSpine in
  peirce_nf hP

/-- **Bridge 9 (Chiral Einstein Anomaly and Spin Frame Dragging)**: -/
theorem grand_bridge_9 (B : Type*) [Ring B] (P : B) (hP : P * P = P) (X Y : B) :
    let N_plus := P * X * (1 - P)
    let N_minus := (1 - P) * Y * P
    let Phi := N_plus + N_minus
    let J := N_plus - N_minus
    let Sigma := N_plus * N_minus - N_minus * N_plus
    let V := N_plus * N_minus + N_minus * N_plus
    let S_P := 2 * P - 1
    S_P * (Phi * J - J * Phi) = -2 * V ∧
    (Sigma * Phi - Phi * Sigma) = 2 * (V * J) :=
  ⟨peirce_chiral_einstein_anomaly P X Y hP, peirce_spin_frame_dragging P X Y hP⟩

/-- **Bridge 9B (Deformed $\mathrm{Cl}(1,1)$ Peirce Algebra, Metric Centrality, Kantor-Jordan Associator,
and Extreme Peirce Defect Owners)**:
In any associative ring $B$ with idempotent $P^2 = P$ and Peirce corners $N_+ = P X (1-P)$, $N_- = (1-P) Y P$:
1. Deformed $\mathrm{Cl}(1,1)$ relations: $\Phi^2 = V$, $J^2 = -V$, $\{\Phi, J\} = 0$, and $\Sigma^2 = V + \delta(V)$.
2. Centrality of the Peirce metric: $P V = V P$, $V N_+ = N_+ V$, and $V N_- = N_- V$.
3. Kantor-Jordan associator identity: $\mathcal{A}_\bullet(N_-, N_+, N_+) = 2 V N_+$.
4. Projects `DefectPeirceChargeAnomaly.idempotency_defect_generates_extreme_peirce_anomaly`. -/
theorem peirce_deformed_cl11_and_jordan_associator {B : Type*} [Ring B]
    (P X Y : B) (hP : P * P = P) :
    let Np := P * X * (1 - P)
    let Nm := (1 - P) * Y * P
    let Phi := Np + Nm
    let J := Np - Nm
    let Sigma := Np * Nm - Nm * Np
    let V := Np * Nm + Nm * Np
    let dV := InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P X Y)
    Phi * Phi = V ∧
    J * J = -V ∧
    Phi * J + J * Phi = 0 ∧
    Sigma * Sigma = V + peirceCurvatureDefect V ∧
    P * V = V * P ∧
    V * Np = Np * V ∧
    V * Nm = Nm * V ∧
    jordanAssociator Nm Np Np = 2 * (V * Np) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm dV
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P X) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm dV
        (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P Y) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.derivSqSig P X Y
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y) -
      InfoGeometry.OperatorAlgebra.PeirceSpine.derivSqJ P X Y
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y) =
        -((4 : ℤ) • (dV * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P X +
          dV * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P Y)) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.derivSqSig P X Y
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) -
      InfoGeometry.OperatorAlgebra.PeirceSpine.derivSqPhi P X Y
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) =
        -((4 : ℤ) • (dV * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P X -
          dV * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P Y))) := by
  dsimp [peirceCurvatureDefect, jordanAssociator, jordanMul]
  open InfoGeometry.OperatorAlgebra.PeirceSpine in
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    idempotency_defect_generates_extreme_peirce_anomaly hP X Y⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · rw [show (2 : B) * ((P * X * (1 - P) * ((1 - P) * Y * P) + (1 - P) * Y * P * (P * X * (1 - P))) *
          (P * X * (1 - P))) =
          (2 : ℤ) • ((P * X * (1 - P) * ((1 - P) * Y * P) + (1 - P) * Y * P * (P * X * (1 - P))) *
          (P * X * (1 - P))) by noncomm_ring]
    peirce_nf hP

/-! ### Clade VIII Completion: Quantum Geometric Tensor, Robertson Bound, & Virasoro Cohomology -/

/-- **Bridge 10 (Chiral Spin Pauli Commutator & Involution Identities)**: -/
theorem grand_bridge_10 :
    let sigX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let sigY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
    sigX * sigY - sigY * sigX = (2 * Complex.I) • pauliZ2 ∧
    sigX * sigX = 1 ∧
    sigY * sigY = 1 := by
  dsimp [pauliZ2]
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring }

/-- **Bridge 10B (Universal Robertson-Schrödinger Quantum Geometric Tensor Bound)**:
In any complex inner product space $H$, for any symmetric $\mathbb{C}$-linear operators
$A, B : H \to_{\mathbb{C}} H$, state $\psi \in H$, and real expectation shifts $a, b \in \mathbb{R}$,
the Berry curvature commutator expectation is bounded by the centered quantum metric variances:
$$\frac{1}{4}\|\langle \psi, [A, B]\psi \rangle\|^2 \le \|(A - a)\psi\|^2 \, \|(B - b)\psi\|^2.$$ -/
theorem robertson_qgt_uncertainty_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y))
    (hB : ∀ x y : H, inner ℂ (B x) y = inner ℂ x (B y))
    (ψ : H) (a b : ℝ) :
    (1 / 4 : ℝ) * ‖inner ℂ ψ (A (B ψ) - B (A ψ))‖ ^ 2 ≤
      ‖A ψ - (a : ℂ) • ψ‖ ^ 2 * ‖B ψ - (b : ℂ) • ψ‖ ^ 2 := by
  let u : H := A ψ - (a : ℂ) • ψ
  let v : H := B ψ - (b : ℂ) • ψ
  have hcomm : inner ℂ u v - inner ℂ v u = inner ℂ ψ (A (B ψ) - B (A ψ)) := by
    change inner ℂ (A ψ - (a : ℂ) • ψ) (B ψ - (b : ℂ) • ψ) -
      inner ℂ (B ψ - (b : ℂ) • ψ) (A ψ - (a : ℂ) • ψ) = _
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    rw [hA ψ (B ψ), hA ψ ψ, hB ψ (A ψ), hB ψ ψ]
    ring
  have htri : ‖inner ℂ u v - inner ℂ v u‖ ≤ ‖inner ℂ u v‖ + ‖inner ℂ v u‖ :=
    norm_sub_le _ _
  have hcs1 : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hcs2 : ‖inner ℂ v u‖ ≤ ‖v‖ * ‖u‖ := norm_inner_le_norm v u
  have hbound : ‖inner ℂ ψ (A (B ψ) - B (A ψ))‖ ≤ 2 * (‖u‖ * ‖v‖) := by
    rw [← hcomm]
    linarith
  have hnn : 0 ≤ ‖inner ℂ ψ (A (B ψ) - B (A ψ))‖ := norm_nonneg _
  have hsq : ‖inner ℂ ψ (A (B ψ) - B (A ψ))‖ ^ 2 ≤ (2 * (‖u‖ * ‖v‖)) ^ 2 := by
    nlinarith
  linarith [show (2 * (‖u‖ * ‖v‖)) ^ 2 = 4 * (‖u‖ ^ 2 * ‖v‖ ^ 2) by ring]

/-- **Spin-1/2 Bloch Purity & Exact Robertson-Berry QGT Defect Law**:
For any spinor $(z_0, z_1) \in \mathbb{C}^2$ with Pauli expectations
$\langle \sigma_x \rangle = 2\operatorname{Re}(\bar{z}_0 z_1)$,
$\langle \sigma_y \rangle = 2\operatorname{Im}(\bar{z}_0 z_1)$,
$\langle \sigma_z \rangle = |z_0|^2 - |z_1|^2$:
1. Exact Bloch purity: $\langle \sigma_x \rangle^2 + \langle \sigma_y \rangle^2 + \langle \sigma_z \rangle^2 = (|z_0|^2 + |z_1|^2)^2$.
2. On normalized spinors ($|z_0|^2 + |z_1|^2 = 1$) with Berry curvature $\Omega_{xy} = -2\langle \sigma_z \rangle$,
   $$\operatorname{Var}(\sigma_x)\operatorname{Var}(\sigma_y) - \frac{1}{4}\Omega_{xy}^2 = \langle \sigma_x \rangle^2 \langle \sigma_y \rangle^2 \ge 0.$$ -/
theorem spinor_bloch_qgt_robertson_defect (z₀ z₁ : ℂ) :
    let expX : ℝ := 2 * (starRingEnd ℂ z₀ * z₁).re
    let expY : ℝ := 2 * (starRingEnd ℂ z₀ * z₁).im
    let expZ : ℝ := Complex.normSq z₀ - Complex.normSq z₁
    let normSq : ℝ := Complex.normSq z₀ + Complex.normSq z₁
    let berryXY : ℝ := -2 * expZ
    expX ^ 2 + expY ^ 2 + expZ ^ 2 = normSq ^ 2 ∧
    (normSq = 1 →
      (1 - expX ^ 2) * (1 - expY ^ 2) - (1 / 4 : ℝ) * berryXY ^ 2 = expX ^ 2 * expY ^ 2 ∧
      (1 / 4 : ℝ) * berryXY ^ 2 ≤ (1 - expX ^ 2) * (1 - expY ^ 2)) := by
  dsimp
  have hPurity :
      (2 * (starRingEnd ℂ z₀ * z₁).re) ^ 2 +
      (2 * (starRingEnd ℂ z₀ * z₁).im) ^ 2 +
      (Complex.normSq z₀ - Complex.normSq z₁) ^ 2 =
      (Complex.normSq z₀ + Complex.normSq z₁) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  refine ⟨hPurity, fun hNorm => ?_⟩
  have hUnit :
      (2 * (starRingEnd ℂ z₀ * z₁).re) ^ 2 +
      (2 * (starRingEnd ℂ z₀ * z₁).im) ^ 2 +
      (Complex.normSq z₀ - Complex.normSq z₁) ^ 2 = 1 := by
    rw [hPurity, hNorm, one_pow]
  have hDefect :
      (1 - (2 * (starRingEnd ℂ z₀ * z₁).re) ^ 2) *
      (1 - (2 * (starRingEnd ℂ z₀ * z₁).im) ^ 2) -
      (1 / 4 : ℝ) * (-2 * (Complex.normSq z₀ - Complex.normSq z₁)) ^ 2 =
      (2 * (starRingEnd ℂ z₀ * z₁).re) ^ 2 * (2 * (starRingEnd ℂ z₀ * z₁).im) ^ 2 := by
    linarith
  refine ⟨hDefect, ?_⟩
  have hNonneg :
      0 ≤ (2 * (starRingEnd ℂ z₀ * z₁).re) ^ 2 * (2 * (starRingEnd ℂ z₀ * z₁).im) ^ 2 := by
    positivity
  linarith

/-- **Bridge 11 (Resonant Heisenberg Current to Virasoro Sugawara Central Extension)**: -/
theorem grand_bridge_11 :
    (∀ (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜],
      ⁅InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Jinf 𝕜 1,
        InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Jinf 𝕜 (-1)⁆ =
        (1 : 𝕜) • InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Kinf 𝕜) ∧
    (∀ (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜],
      ⁅InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Jinf 𝕜 (-1),
        InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Jinf 𝕜 1⁆ =
        ((-1 : Int) : 𝕜) • InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Kinf 𝕜) :=
  VirasoroProject.Extensions.PrimeVirasoroSugawara.canonicalCurrentCurrentLevelOneEvidence

/-- Gelfand-Fuks / Virasoro central 2-cocycle $\omega_{\mathrm{Vir}}(m, n) = \delta_{m+n,0}\frac{m^3 - m}{12}$
on the Witt algebra $[L_m, L_n] = (m - n) L_{m+n}$. -/
def virasoroCocycle (m n : ℤ) : ℚ :=
  if m + n = 0 then ((m : ℚ) ^ 3 - (m : ℚ)) / 12 else 0

/-- Chevalley-Eilenberg 1-coboundary $(\delta f)(m, n) = (m - n) f(m + n)$ on the Witt algebra. -/
def wittCoboundary (f : ℤ → ℚ) (m n : ℤ) : ℚ :=
  ((m : ℚ) - (n : ℚ)) * f (m + n)

/-- **Bridge 11B (Virasoro 2-Cocycle Jacobi Law, $\mathfrak{sl}_2$ Protection, $H^2(\mathcal{W},\mathbb{Q}) \ne 0$,
and Certified Sugawara $c = 1$ Owner Readback)**:
1. Skew-symmetry: $\omega_{\mathrm{Vir}}(m, n) = -\omega_{\mathrm{Vir}}(n, m)$.
2. Chevalley-Eilenberg Jacobi 2-cocycle identity for all $m, n, k \in \mathbb{Z}$.
3. Exact global conformal $\mathfrak{sl}_2$ anomaly-freeness: $\omega_{\mathrm{Vir}}(m, -m) = 0 \iff m \in \{-1, 0, 1\}$.
4. Cohomological non-triviality: $\omega_{\mathrm{Vir}}$ is not equal to `wittCoboundary f` for any $f : \mathbb{Z} \to \mathbb{Q}$.
5. Certified repository Sugawara readback: `heisenberg_sugawara_centralCharge_eq_one` and `virasoro_project_owner_certified`. -/
theorem virasoro_cocycle_cohomology :
    (∀ m n : ℤ, virasoroCocycle m n = -virasoroCocycle n m) ∧
    (∀ m n k : ℤ,
      ((m : ℚ) - (n : ℚ)) * virasoroCocycle (m + n) k +
      ((n : ℚ) - (k : ℚ)) * virasoroCocycle (n + k) m +
      ((k : ℚ) - (m : ℚ)) * virasoroCocycle (k + m) n = 0) ∧
    (∀ m : ℤ, virasoroCocycle m (-m) = 0 ↔ m = -1 ∨ m = 0 ∨ m = 1) ∧
    (¬ ∃ f : ℤ → ℚ, virasoroCocycle = wittCoboundary f) ∧
    InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1 ∧
    (∃ V : InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.VirasoroDatum (VirasoroProject.VirasoroAlgebra ℝ),
      InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.VirasoroProjectRealizes V) := by
  refine ⟨?_, ?_, ?_, ?_,
    VirasoroProject.Extensions.PrimeVirasoroSugawara.heisenberg_sugawara_centralCharge_eq_one,
    VirasoroProject.Extensions.PrimeVirasoroSugawara.virasoro_project_owner_certified⟩
  · intro m n
    dsimp [virasoroCocycle]
    by_cases h : m + n = 0
    · have hnm : n + m = 0 := by omega
      have hn : n = -m := by omega
      simp only [h, hnm, ↓reduceIte]
      rw [hn]
      push_cast
      ring
    · have hnm : n + m ≠ 0 := by omega
      simp only [h, hnm, ↓reduceIte, neg_zero]
  · intro m n k
    dsimp [virasoroCocycle]
    by_cases h : m + n + k = 0
    · have h1 : (m + n) + k = 0 := h
      have h2 : (n + k) + m = 0 := by omega
      have h3 : (k + m) + n = 0 := by omega
      have hk : k = -(m + n) := by omega
      simp only [h1, h2, h3, ↓reduceIte]
      rw [hk]
      push_cast
      ring
    · have h1 : (m + n) + k ≠ 0 := h
      have h2 : (n + k) + m ≠ 0 := by omega
      have h3 : (k + m) + n ≠ 0 := by omega
      simp only [h1, h2, h3, ↓reduceIte]
      ring
  · intro m
    dsimp [virasoroCocycle]
    have hm0 : m + -m = 0 := add_neg_cancel m
    simp only [hm0, ↓reduceIte]
    constructor
    · intro h
      have hfac : ((m : ℚ) + 1) * ((m : ℚ) * ((m : ℚ) - 1)) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with hm1 | hrest
      · left
        have hm : (m : ℚ) = ((-1 : ℤ) : ℚ) := by push_cast; linarith
        exact Int.cast_injective hm
      · rcases mul_eq_zero.mp hrest with hm_zero | hmp1
        · right; left
          have hm : (m : ℚ) = ((0 : ℤ) : ℚ) := by push_cast; linarith
          exact Int.cast_injective hm
        · right; right
          have hm : (m : ℚ) = ((1 : ℤ) : ℚ) := by push_cast; linarith
          exact Int.cast_injective hm
    · rintro (rfl | rfl | rfl) <;> norm_num
  · rintro ⟨f, hf⟩
    have h1 := congrFun (congrFun hf 1) (-1)
    have h2 := congrFun (congrFun hf 2) (-2)
    simp only [virasoroCocycle, wittCoboundary] at h1 h2
    norm_num at h1 h2
    linarith

/-! ### Clades III, IV, & IX: Infinite Sewing, KMS Crystallization, & Omega Bridges -/

/-- **Bridge 12 (Doubled Pauli Group Homomorphism to Infinite Hilbert Boundary Sewing)**: -/
theorem grand_bridge_12 :
    (∀ g h : Multiplicative (ZMod 2 × ZMod 2),
      doubledPauliHom (g * h) = doubledPauliHom g * doubledPauliHom h) ∧
    (∀ (B : ConcreteHilbertCommutation.H_lp ℝ →L[ℝ] ConcreteHilbertCommutation.H_lp ℝ),
      (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
          (B.comp (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) = B →
      inner ℝ ConcreteHilbertSewnAnomaly.canonicalCantorSewnState
          (((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp B)
            ConcreteHilbertSewnAnomaly.canonicalCantorSewnState) = 0) :=
  ⟨fun g h => map_mul doubledPauliHom g h,
   fun B hB => ConcreteHilbertSewnAnomaly.canonicalCantorSewnState_chiral_zero B hB⟩

/-- **Bridge 13 (McKean-Singer Heat-Kernel Supertrace Invariance to Bost-Connes Witten Index)**: -/
theorem grand_bridge_13
    (s : ℂ) (N : ℕ) (c : ℕ → ℂ) (hc0 : c 0 = 1) (t : ℂ)
    (β : ℝ) (hβ : 1 < β) :
    superTrace grading3 (heatKernelPoly N c t (diracJump3 s)) = 1 ∧
    L ↗ArithmeticFunction.moebius (β : ℂ) = (riemannZeta (β : ℂ))⁻¹ :=
  bridge_mckean_singer_to_witten_zeta s N c hc0 t β hβ

/-- **Bridge 14 (Liouville Parity KMS Flow Commutation to Zero-Temperature Boundary Crystallization)**: -/
theorem grand_bridge_14 :
    (∀ (t : ℝ) (n : ℕ),
      (InfoGeometry.BostConnes.liouvilleParity n : ℂ) *
          BostConnesThermofield.modular_phase t n =
        BostConnesThermofield.modular_phase t n *
          (InfoGeometry.BostConnes.liouvilleParity n : ℂ)) ∧
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 1) :=
  bridge_thermal_protection_to_boundary_sewing

/-- **Bridge 15 (Omega Parry Transfer Operator Jordan Nilpotence to BRST / Oblique Defects)**: -/
theorem grand_bridge_15 :
    Omega.Folding.gaugeAnomalyMinusHalfMatrix.mulVec
        Omega.Folding.gaugeAnomalyMinusHalfEigenvector = 0 ∧
    Omega.Folding.gaugeAnomalyMinusHalfMatrix.mulVec
        Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector =
      Omega.Folding.gaugeAnomalyMinusHalfEigenvector ∧
    brstQ2 * brstQ2 = 0 ∧
    GenericObliqueIdempotentAnomaly.E01 (R := ℂ) *
        GenericObliqueIdempotentAnomaly.E01 = 0 := by
  have hBlock := Omega.Folding.paper_fold_gauge_anomaly_jordan_fingerprint.2
  refine ⟨hBlock.1, hBlock.2.1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [brstQ2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GenericObliqueIdempotentAnomaly.E01, Matrix.single, Matrix.mul_apply]

/-- Polymorphic $2 \times 2$ matrix non-commutativity witness over any nontrivial ring $R$ (`('2', '2', 'R')`). -/
theorem mat2_polymorphic_not_commute {R : Type*} [Ring R] [Nontrivial R] :
    ∃ x y : Matrix (Fin 2) (Fin 2) R, x * y ≠ y * x := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- **Bridge 15B (Universal Injective Equivariant BRST-Jordan Intertwiner)**:
Over any integral domain $R$, any generalized Jordan chain $M v_0 = 0$, $M v_1 = v_0$ with $v_0 \ne 0$
satisfies strict index-2 nilpotence ($M v_1 \ne 0$, $(M^2) v_1 = 0$) and admits an injective
equivariant intertwiner $\iota : (\mathrm{Fin}\;2 \to R) \hookrightarrow (m \to R)$ from the $2 \times 2$
BRST nilpotent cell $Q_2 = !![0, 1; 0, 0]$: $M(\iota c) = \iota(Q_2 c)$. -/
theorem jordan_chain_brst_intertwiner
    {m R : Type*} [Fintype m] [DecidableEq m] [CommRing R] [IsDomain R]
    (M : Matrix m m R) (v₀ v₁ : m → R)
    (hv₀ : v₀ ≠ 0) (hM0 : M.mulVec v₀ = 0) (hM1 : M.mulVec v₁ = v₀) :
    let Q₂ : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
    let ι : (Fin 2 → R) → (m → R) := fun c => c 0 • v₀ + c 1 • v₁
    M.mulVec v₁ ≠ 0 ∧
    (M * M).mulVec v₁ = 0 ∧
    (∀ c : Fin 2 → R, M.mulVec (ι c) = ι (Q₂.mulVec c)) ∧
    Function.Injective ι := by
  dsimp
  refine ⟨by rw [hM1]; exact hv₀, ?_, ?_, ?_⟩
  · first
    | rw [Matrix.mulVec_mulVec, hM1, hM0]
    | rw [← Matrix.mulVec_mulVec, hM1, hM0]
  · intro c
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM0, hM1]
    have hQ0 : ((!![0, (1 : R); 0, 0] : Matrix (Fin 2) (Fin 2) R).mulVec c) 0 = c 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hQ1 : ((!![0, (1 : R); 0, 0] : Matrix (Fin 2) (Fin 2) R).mulVec c) 1 = 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hQ0, hQ1, smul_zero, zero_add, zero_smul, add_zero]
  · intro a b hab
    have hdiff : (a 0 - b 0) • v₀ + (a 1 - b 1) • v₁ = 0 := by
      ext i
      have hi := congrFun hab i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      calc (a 0 - b 0) * v₀ i + (a 1 - b 1) * v₁ i
          = (a 0 * v₀ i + a 1 * v₁ i) - (b 0 * v₀ i + b 1 * v₁ i) := by ring
        _ = 0 := by rw [hi, sub_self]
    have hMdiff : M.mulVec ((a 0 - b 0) • v₀ + (a 1 - b 1) • v₁) = 0 := by
      rw [hdiff, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM0, hM1,
        smul_zero, zero_add] at hMdiff
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : m, v₀ i₀ ≠ 0 := by
      by_contra hall
      exact hv₀ (funext fun i => Classical.not_not.mp fun hni => hall ⟨i, hni⟩)
    have hc1_mul : (a 1 - b 1) * v₀ i₀ = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hMdiff i₀
    have hc1 : a 1 - b 1 = 0 := (mul_eq_zero.mp hc1_mul).resolve_right hi₀
    rw [hc1, zero_smul, add_zero] at hdiff
    have hc0_mul : (a 0 - b 0) * v₀ i₀ = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hdiff i₀
    have hc0 : a 0 - b 0 = 0 := (mul_eq_zero.mp hc0_mul).resolve_right hi₀
    ext j
    fin_cases j
    · exact sub_eq_zero.mp hc0
    · exact sub_eq_zero.mp hc1

/-- Concrete instantiation of the injective BRST-Jordan intertwiner on the Omega Parry transfer defect. -/
theorem omega_parry_brst_intertwiner :
    let M := Omega.Folding.gaugeAnomalyMinusHalfMatrix
    let v₀ := Omega.Folding.gaugeAnomalyMinusHalfEigenvector
    let v₁ := Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector
    M.mulVec v₁ ≠ 0 ∧
    (M * M).mulVec v₁ = 0 ∧
    Function.Injective (fun c : Fin 2 → ℚ => c 0 • v₀ + c 1 • v₁) := by
  have hv₀ : Omega.Folding.gaugeAnomalyMinusHalfEigenvector ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simp [Omega.Folding.gaugeAnomalyMinusHalfEigenvector] at h1
  have hBlock := Omega.Folding.paper_fold_gauge_anomaly_jordan_fingerprint.2
  have hInt := jordan_chain_brst_intertwiner
    Omega.Folding.gaugeAnomalyMinusHalfMatrix
    Omega.Folding.gaugeAnomalyMinusHalfEigenvector
    Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector
    hv₀ hBlock.1 hBlock.2.1
  exact ⟨hInt.1, hInt.2.1, hInt.2.2.2⟩

/-- **Bridge 16 (Omega POM Rewriting 1-Cochains Modulo Boundary Shifts to Bulk-Boundary Cancellation)**: -/
theorem grand_bridge_16
    {W C A Q : Type*} [AddGroup A] [AddGroup Q]
    (classOf : A → Q) (hadd : ∀ x y, classOf (x + y) = classOf x + classOf y)
    (hzero : classOf 0 = 0) (boundary : C → A) (anom anom' : W → A)
    (hchange : ∀ w, ∃ c, anom' w = anom w + boundary c)
    (hboundary : ∀ c, classOf (boundary c) = 0)
    {R : Type*} [Ring R] [StarRing R] (sys : Cuntz2System R)
    {M : Type*} [AddCommGroup M] (tr : CyclicTrace R M)
    (D X : R) :
    (∀ w, classOf (anom w) = 0 ↔ classOf (anom' w) = 0) ∧
    totalGreenSchwarzAnomaly sys tr D X = 0 :=
  ⟨Omega.POM.paper_pom_anom_cohomology_class
      classOf hadd hzero boundary anom anom' hchange hboundary,
   green_schwarz_inflow_cancellation sys tr D X⟩

/-- Canonical descent of a symmetric bilinear form $B : V \to_R V \to_R R$ to its radical quotient
`Quotient (Setoid.ker B)`. -/
def descendSymmetricPairing {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] R) (hSym : ∀ x y : V, B x y = B y x) :
    Quotient (Setoid.ker B) → Quotient (Setoid.ker B) → R :=
  fun q₁ q₂ => Quotient.liftOn₂ q₁ q₂ (fun x y => B x y) fun x₁ y₁ x₂ y₂ hx hy => by
    change B x₁ = B x₂ at hx
    change B y₁ = B y₂ at hy
    calc B x₁ y₁ = B x₂ y₁ := by rw [hx]
      _ = B y₁ x₂ := hSym x₂ y₁
      _ = B y₂ x₂ := by rw [hy]
      _ = B x₂ y₂ := hSym y₂ x₂

/-- **Bridge 16B (Canonical Radical-Quotient Non-Degenerate Descent)**:
Quotienting a module $V$ by the null radical $\ker B$ of a symmetric bilinear form $B$
identifies vectors modulo $\ker B$ and induces a strictly non-degenerate pairing on the quotient. -/
theorem radical_quotient_nondegenerate {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] R) (hSym : ∀ x y : V, B x y = B y x) :
    (∀ x y : V, x - y ∈ LinearMap.ker B ↔
      Quotient.mk (Setoid.ker B) x = Quotient.mk (Setoid.ker B) y) ∧
    (∀ q : Quotient (Setoid.ker B),
      (∀ r : Quotient (Setoid.ker B), descendSymmetricPairing B hSym q r = 0) ↔
        q = Quotient.mk (Setoid.ker B) 0) := by
  constructor
  · intro x y
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, Quotient.eq]
    rfl
  · intro q
    induction q using Quotient.inductionOn with
    | h x =>
      constructor
      · intro hAll
        apply Quotient.sound
        change B x = B 0
        ext y
        simpa [descendSymmetricPairing] using hAll (Quotient.mk (Setoid.ker B) y)
      · intro hZero r
        induction r using Quotient.inductionOn with
        | h y =>
          rw [hZero]
          simp [descendSymmetricPairing]

/-- Specialization of `su2MixedAnomalyParam Nc YQ` to empirical quark hypercharge $Y_Q = 1/6$
(see `chiral_hypercharge_color_reciprocity` for the non-circular law $N_c Y_Q = 1/2$). -/
def su2MixedAnomaly (Nc : ℚ) : ℚ := 2 * Nc * (1 / 6) + 2 * (-1 / 2)

/-- Mixed gravitational-hypercharge $\mathrm{Grav}^2 U(1)_Y$ anomaly for color multiplicity $N_c$. -/
def gravHyperchargeAnomaly (Nc : ℚ) : ℚ :=
  Nc * (2 * (1 / 6) - (2 / 3) - (-1 / 3)) + (2 * (-1 / 2) - (-1))

/-- Cubic abelian $U(1)_Y^3$ chiral gauge anomaly for color multiplicity $N_c$. -/
def u1CubicAnomaly (Nc : ℚ) : ℚ :=
  Nc * (2 * (1 / 6) ^ 3 - (2 / 3) ^ 3 - (-1 / 3) ^ 3) + (2 * (-1 / 2) ^ 3 - (-1) ^ 3)

/-- Foundational-axiom proof of `Omega.GU.window6ThreeFamilyZeroAnom` avoiding `native_decide`. -/
theorem window6ThreeFamilyZeroAnom_pure : Omega.GU.window6ThreeFamilyZeroAnom := by
  refine ⟨by simp [Omega.Conclusion.zeroVisibleAnomaly],
          Omega.Conclusion.Window6BoundaryQuotientCyclicCardinality.boundary_set_cardinality, ?_⟩
  intro Nf _δ _hGeom _hNe hTop
  have hf9 : Nat.fib 9 = 34 := rfl
  have hf10 : Nat.fib 10 = 55 := rfl
  rw [hf9, hf10] at hTop
  omega

/-- **Bridge 17 (Omega Complete Corridor Synthesis: Window-6 Three-Family Selection, $N_c = 3$ Chiral
Hypercharge Cancellation, Reduced Determinant Ratio, & Canonical Quotient Hilbertization)**:
Unifies `Omega.CircleDimension`, `Omega.Zeta.FinitePartMomentAnomalyReducedDeterminantRatio`,
`Omega.Conclusion.AnomalyQuotientCanonicalHilbertization`, and `Omega.GU.Window6ThreeFamilyZeroAnom`
with standard chiral hypercharge gauge/gravitational cancellation:
1. `anomalyConnectedDim 4 0 = 6` ($\binom{4}{2} = \dim \mathfrak{so}(4) = 6$), with balanced chiral bivector rank $3 + 3 = 6$ ($\mathfrak{su}(2)_L \oplus \mathfrak{su}(2)_R$).
2. $\mathrm{Grav}^2 U(1)_Y = 0$ identically, while $SU(2)_L^2 U(1)_Y = 0 \wedge U(1)_Y^3 = 0 \iff N_c = 3$.
3. Reduced determinant ratio logarithmic anomaly law (`paper_finite_part_moment_anomaly_reduced_determinant_ratio`).
4. Canonical quotient Hilbertization multi-axis filtering (`paper_conclusion_anomaly_quotient_canonical_hilbertization`).
5. Foundational proof of `Omega.GU.window6ThreeFamilyZeroAnom`. -/
theorem grand_bridge_17 :
    Omega.CircleDimension.anomalyConnectedDim 4 0 = 6 ∧
    (∀ Np Nm : ℕ,
      Np + Nm = Omega.CircleDimension.anomalyConnectedDim 4 0 ∧ Np = Nm ↔ Np = 3 ∧ Nm = 3) ∧
    (∀ Nc : ℚ, gravHyperchargeAnomaly Nc = 0) ∧
    (∀ Nc : ℚ, su2MixedAnomaly Nc = 0 ∧ u1CubicAnomaly Nc = 0 ↔ Nc = 3) ∧
    (∀ (q : ℕ) (_hq : 2 ≤ q) (C1 Cq det1 detq : ℝ) (_hC1 : C1 = det1⁻¹) (_hCq : Cq = detq⁻¹),
      Real.log Cq - (q : ℝ) * Real.log C1 = -Real.log detq + (q : ℝ) * Real.log det1) ∧
    (∀ {ι : Type} [DecidableEq ι] (axes : Finset ι) (f : Finset ι → ℝ),
      Omega.Conclusion.conclusion_anomaly_quotient_canonical_hilbertization_normSq axes f =
        Finset.sum (axes.powerset.filter (fun S => 2 ≤ S.card)) fun S => f S ^ 2) ∧
    Omega.GU.window6ThreeFamilyZeroAnom := by
  have hWin6 : Omega.CircleDimension.anomalyConnectedDim 4 0 = 6 := by
    rw [(grand_bridge_7 4 0).1]
    decide
  refine ⟨hWin6, ?_, ?_, ?_,
    Omega.Zeta.paper_finite_part_moment_anomaly_reduced_determinant_ratio,
    fun axes f => (Omega.Conclusion.paper_conclusion_anomaly_quotient_canonical_hilbertization axes f).2.2,
    window6ThreeFamilyZeroAnom_pure⟩
  · intro Np Nm
    rw [hWin6]
    omega
  · intro Nc
    unfold gravHyperchargeAnomaly
    ring
  · intro Nc
    constructor
    · rintro ⟨h1, _⟩
      unfold su2MixedAnomaly at h1
      linarith
    · rintro rfl
      unfold su2MixedAnomaly u1CubicAnomaly
      norm_num

/-! ## Part V: The Multi-Level Double Socratic Aporia Theorem -/

/-- **Multi-Level Double Socratic Aporia Theorem**:
Formalizes the two core dialectical antinomies across the repository's expanded anomaly corridors:
- **Aporia I**: Local oblique non-commutativity (`commutator oblique leftProjector ≠ 0`) vs. global
  sewn boundary annihilation (`⟨ψ₀, ε_lp (B ψ₀)⟩ = 0`), mediated by ungraded trace vanishing and
  graded supertrace doubling on odd commutators.
- **Aporia II**: Finite-dimensional Dirac kernel jumping (`3 → 1`) with rigid supertrace index `1`
  vs. infinite-dimensional Cuntz $O_2$ branch non-commutativity (`S_L ∘ S_R ≠ S_R ∘ S_L`) with
  strict modular sewing invariance (`J S_i J = S_i`). -/
theorem multi_level_double_socratic_aporia :
    (GenericObliqueIdempotentAnomaly.commutator
        (GenericObliqueIdempotentAnomaly.oblique (R := ℂ))
        GenericObliqueIdempotentAnomaly.leftProjector ≠ 0 ∧
     (∀ (B : ConcreteHilbertCommutation.H_lp ℝ →L[ℝ] ConcreteHilbertCommutation.H_lp ℝ),
       (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
           (B.comp (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) = B →
       inner ℝ ConcreteHilbertSewnAnomaly.canonicalCantorSewnState
           (((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp B)
             ConcreteHilbertSewnAnomaly.canonicalCantorSewnState) = 0) ∧
     (∀ (A B : Matrix (Fin 2) (Fin 2) ℂ),
       A 0 0 = 0 → A 1 1 = 0 → B 0 0 = 0 → B 1 1 = 0 →
       Matrix.trace (A * B - B * A) = 0 ∧
       Matrix.trace (pauliZ2 * (A * B - B * A)) = 2 * Matrix.trace (pauliZ2 * (A * B)))) ∧
    ((Matrix.mulVec (diracJump3 0) ![1, 0, 0] = 0 ∧
      Matrix.mulVec (diracJump3 1) ![1, 0, 0] ≠ 0 ∧
      superTrace grading3 (heatKernelPoly 0 (fun _ => 1) 0 (diracJump3 1)) = 1) ∧
     ((ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)).comp
          (ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)) ≠
        (ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)).comp
          (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) ∧
      (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
          ((ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)).comp
            (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) =
        ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ) ∧
      (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
          ((ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)).comp
            (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) =
        ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ))) := by
  constructor
  · refine ⟨GenericObliqueIdempotentAnomaly.oblique_commutator_nonzero,
            fun B hB => ConcreteHilbertSewnAnomaly.canonicalCantorSewnState_chiral_zero B hB,
            fun A B hA0 hA1 hB0 hB1 => grand_bridge_4 A B hA0 hA1 hB0 hB1⟩
  · constructor
    · have hJump := diracJump3_invariant_index 1 0 (fun _ => 1) rfl 0
      have h1 := (hJump.2.2.2.1 one_ne_zero).1
      exact ⟨hJump.2.2.1.1, h1, hJump.2.2.2.2⟩
    · exact ⟨ConcreteHilbertSewnAnomaly.S_left_right_lp_clm_noncomm,
             ConcreteHilbertSewnAnomaly.S_left_lp_clm_sewn_invariant (E := ℝ),
             ConcreteHilbertSewnAnomaly.S_right_lp_clm_sewn_invariant (E := ℝ)⟩

/-! ## Part VI: Concrete Non-Trivial Realization Witnesses for All Nine Clades -/

/-- Top-level complex matrix nilpotent unit witness for OpenGauss T16 non-commutativity. -/
def matN : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Top-level complex matrix nilpotent adjoint witness for OpenGauss T16 non-commutativity. -/
def matNstar : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- Explicit non-commutativity witness for complex $2 \times 2$ matrices (`('2', '2', 'ℂ')`). -/
theorem matN_matNstar_not_commute : matN * matNstar ≠ matNstar * matN := by
  intro h
  have hentry := congrFun (congrFun h 0) 0
  simp only [matN, matNstar, Matrix.mul_apply, Fin.sum_univ_two] at hentry
  norm_num at hentry

/-- Realization Witness 1 (Clade I): The oblique projector commutator is strictly non-zero. -/
theorem witness_cladeI_oblique_commutator_ne_zero :
    GenericObliqueIdempotentAnomaly.commutator
        (GenericObliqueIdempotentAnomaly.oblique (R := ℂ))
        GenericObliqueIdempotentAnomaly.leftProjector ≠ 0 :=
  GenericObliqueIdempotentAnomaly.oblique_commutator_nonzero

/-- Realization Witness 2 (Clade II): The Pauli projective representation has an irremovable obstruction. -/
theorem witness_cladeII_pauli_projective_obstruction :
    ∀ (b : ZMod 2 × ZMod 2 → ℂˣ),
      ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Matrix (Fin 2) (Fin 2) ℂ)) *
          ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Matrix (Fin 2) (Fin 2) ℂ)) ≠
        ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Matrix (Fin 2) (Fin 2) ℂ)) *
          ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Matrix (Fin 2) (Fin 2) ℂ)) :=
  pauliProjUnit_anomaly_irremovable

/-- Realization Witness 3 (Clade III): The Cuntz $O_2$ branch isometries strictly fail to commute. -/
theorem witness_cladeIII_cuntz_O2_noncommuting :
    (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)) ≠
      (ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) :=
  ConcreteHilbertSewnAnomaly.S_left_right_lp_clm_noncomm

/-- Realization Witness 4 (Clade IV): Regular convergent Bost-Connes Witten index evaluation at $\beta = 2$
(contrasted with the critical $\beta = 1$ pole and $\beta \to 1^+$ Souriau Fisher blow-up in
`bost_connes_regular_vs_critical_pole_dichotomy`). -/
theorem witness_cladeIV_bost_connes_zeta_singular :
    L ↗ArithmeticFunction.moebius (2 : ℂ) = (riemannZeta (2 : ℂ))⁻¹ :=
  SouriauBostConnesTransition.bostConnes_witten_index_eq_reciprocal_zeta 2 (by norm_num)

/-- Realization Witness 5 (Clade V): Green-Schwarz inflow cancellation holds universally. -/
theorem witness_cladeV_green_schwarz_inflow_cancellation
    {R : Type*} [Ring R] [StarRing R] (sys : Cuntz2System R)
    {M : Type*} [AddCommGroup M] (tr : CyclicTrace R M)
    (D X : R) :
    totalGreenSchwarzAnomaly sys tr D X = 0 :=
  green_schwarz_inflow_cancellation sys tr D X

/-- Top-level real matrix witness for OpenGauss T16 non-commutativity. -/
def matZplus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Top-level real matrix lower-triangular witness for OpenGauss T16 non-commutativity. -/
def matZminus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- Explicit non-commutativity witness for real $2 \times 2$ matrices (`('2', '2', 'ℝ')`). -/
theorem matZplus_matZminus_not_commute : matZplus * matZminus ≠ matZminus * matZplus := by
  intro h
  have hentry := congrFun (congrFun h 0) 0
  simp only [matZplus, matZminus, Matrix.mul_apply, Fin.sum_univ_two] at hentry
  norm_num at hentry

/-- Realization Witness 6 (Clade VI): Non-commuting $\mathfrak{so}(5,5)$ grade-$+1$ TKK generators
producing a non-zero grade-$+2$ Heisenberg center $[P_{+1}, Q_{+1}] = Z_{+2} \ne 0$. -/
theorem witness_cladeVI_heisenberg_sl2_commutator :
    matZplus * matZminus - matZminus * matZplus ≠ 0 ∧
    so55Grade1P * so55Grade1Q - so55Grade1Q * so55Grade1P ≠ 0 := by
  constructor
  · intro h
    have hentry := congrFun (congrFun h 0) 0
    simp only [matZplus, matZminus, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.zero_apply, Fin.sum_univ_two] at hentry
    norm_num at hentry
  · rw [grand_bridge_8_so55_five_grading.2.2.2.2.2.2.1]
    exact grand_bridge_8_so55_five_grading.2.2.2.2.2.1

/-- Realization Witness 7 (Clade VII): Non-zero Peirce spin frame dragging and Jordan associator. -/
theorem witness_cladeVII_peirce_einstein_cartan_dragging :
    let N_plus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let N_minus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let Phi := N_plus + N_minus
    let Sigma := N_plus * N_minus - N_minus * N_plus
    Sigma * Phi - Phi * Sigma ≠ 0 ∧
    jordanAssociator N_minus N_plus N_plus ≠ 0 := by
  dsimp [jordanAssociator, jordanMul]
  constructor
  · intro h
    have hentry := congrFun (congrFun h 0) 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two] at hentry
    norm_num at hentry
  · intro h
    have hentry := congrFun (congrFun h 0) 1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.zero_apply, Fin.sum_univ_two] at hentry
    norm_num at hentry

/-- Realization Witness 7B (Clade VII Multi-Channel Gap Additivity Witness):
Projects the concrete $4 \times 4$ two-channel non-commutative matrix witness from `MultiChannelAnomalyGapPoset`. -/
theorem witness_cladeVII_multi_channel_additive_gap :
    InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.Gap
      (InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mcMatrixNa +
       InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mcMatrixNb) =
    InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.Gap
      InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mcMatrixNa +
    InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.Gap
      InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mcMatrixNb ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.Gap
      (InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mcMatrixNa +
       InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mcMatrixNb) ≠ 0 := by
  have h := InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset.mc_matrix_noncomm_and_additive_gap_witness
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Realization Witness 8 (Clade VIII): Mode-$2$ Virasoro cocycle activation and non-coboundary proof. -/
theorem witness_cladeVIII_virasoro_level_two_anomaly :
    virasoroCocycle 2 (-2) = 1 / 2 ∧
    virasoroCocycle 2 (-2) ≠ 0 ∧
    ¬ ∃ f : ℤ → ℚ, virasoroCocycle = wittCoboundary f := by
  refine ⟨?_, ?_, virasoro_cocycle_cohomology.2.2.2.1⟩
  · simp [virasoroCocycle]
    norm_num
  · simp [virasoroCocycle]
    norm_num

/-- Realization Witness 9 (Clade IX): The Omega Parry transfer matrix Jordan chain is non-trivial
and embeds the $2 \times 2$ BRST differential injectively. -/
theorem witness_cladeIX_omega_jordan_nilpotent_cell :
    Omega.Folding.gaugeAnomalyMinusHalfEigenvector ≠ 0 ∧
    Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector ≠ 0 ∧
    Omega.Folding.gaugeAnomalyMinusHalfMatrix.mulVec
        Omega.Folding.gaugeAnomalyMinusHalfEigenvector = 0 ∧
    Omega.Folding.gaugeAnomalyMinusHalfMatrix.mulVec
        Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector =
      Omega.Folding.gaugeAnomalyMinusHalfEigenvector := by
  have hBlock := Omega.Folding.paper_fold_gauge_anomaly_jordan_fingerprint.2
  refine ⟨?_, ?_, hBlock.1, hBlock.2.1⟩
  · intro h
    have h1 := congrFun h 1
    simp [Omega.Folding.gaugeAnomalyMinusHalfEigenvector] at h1
  · intro h
    have h2 := congrFun h 2
    simp [Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector] at h2


/-! ## Part VII: SOLVE-COAGULA Forensic Reconciliation: Signature Dichotomy, Reciprocity, Cl(4,4) Krein Ceiling, Functorial Spine, & 15-Node Causal Poset -/

/-- Split real Krein symmetric bilinear form $\eta_{\mathbb{R}}(x, y) = x_0 y_0 - x_1 y_1$ on $\mathbb{R}^2$. -/
def kreinRealForm2 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x 0 * y 0 - x 1 * y 1)
    (fun x₁ x₂ y => by simp; ring)
    (fun c x y => by simp; ring)
    (fun x y₁ y₂ => by simp; ring)
    (fun c x y => by simp; ring)

/-- Split complex Krein indefinite inner pairing $\langle u, v \rangle_\eta = \bar{u}_0 v_0 - \bar{u}_1 v_1$ on $\mathbb{C}^2$. -/
def kreinInnerC2 (u v : Fin 2 → ℂ) : ℂ :=
  star (u 0) * v 0 - star (u 1) * v 1

/-- **Deduction 1 (Krein Falsification of Robertson QGT & Null-Cone Survival Under Radical Quotient)**:
Proves that Hilbert positivity is strictly necessary for `robertson_qgt_uncertainty_bound`:
1. On $(\mathbb{R}^2, \eta = \mathrm{diag}(1, -1))$, $\ker \eta = \bot$, so radical quotienting is trivial
   yet the non-zero null vector $\psi_{\mathbb{R}} = (1, 1)^\top$ satisfies $\eta(\psi_{\mathbb{R}}, \psi_{\mathbb{R}}) = 0$.
2. On $(\mathbb{C}^2, \langle \cdot, \cdot \rangle_\eta)$, $A = \sigma_z$ and $B = i\sigma_x$ are $\eta$-self-adjoint,
   $\langle A\psi, A\psi \rangle_\eta = \langle B\psi, B\psi \rangle_\eta = 0$ on $\psi = (1, 1)^\top$, while
   $\frac{1}{4}\|\langle \psi, [A, B]\psi \rangle_\eta\|^2 = 4 \not\le 0$. -/
theorem krein_robertson_qgt_counterexample_and_null_cone_survival :
    LinearMap.ker kreinRealForm2 = ⊥ ∧
    (let ψR : Fin 2 → ℝ := ![1, 1]
     ψR ≠ 0 ∧ kreinRealForm2 ψR ψR = 0) ∧
    (let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
     let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]
     let ψ : Fin 2 → ℂ := ![1, 1]
     (∀ x y : Fin 2 → ℂ, kreinInnerC2 (A.mulVec x) y = kreinInnerC2 x (A.mulVec y)) ∧
     (∀ x y : Fin 2 → ℂ, kreinInnerC2 (B.mulVec x) y = kreinInnerC2 x (B.mulVec y)) ∧
     kreinInnerC2 (A.mulVec ψ) (A.mulVec ψ) = 0 ∧
     kreinInnerC2 (B.mulVec ψ) (B.mulVec ψ) = 0 ∧
     (1 / 4 : ℝ) * ‖kreinInnerC2 ψ ((A * B - B * A).mulVec ψ)‖ ^ 2 = 4 ∧
     ¬ ((1 / 4 : ℝ) * ‖kreinInnerC2 ψ ((A * B - B * A).mulVec ψ)‖ ^ 2 ≤ 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h0 : kreinRealForm2 x ![1, 0] = 0 := by rw [hx]; rfl
    have h1 : kreinRealForm2 x ![0, 1] = 0 := by rw [hx]; rfl
    simp [kreinRealForm2] at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1]
  · constructor
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · simp [kreinRealForm2]
  · have hval : kreinInnerC2 ![1, 1]
        (((!![1, (0 : ℂ); 0, -1] * !![0, Complex.I; Complex.I, 0] -
           !![0, Complex.I; Complex.I, 0] * !![1, (0 : ℂ); 0, -1]).mulVec) ![1, 1]) =
        4 * Complex.I := by
      simp [kreinInnerC2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp [kreinInnerC2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · intro x y
      simp [kreinInnerC2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.conj_I]
      ring
    · simp [kreinInnerC2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [kreinInnerC2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.conj_I]
    · rw [hval, norm_mul, Complex.norm_I, mul_one]
      norm_num
    · rw [hval, norm_mul, Complex.norm_I, mul_one]
      norm_num

/-- **Deduction 3 (Finite-Matrix Tracial Wall Against Central Identity Commutators)**:
In characteristic zero, no non-empty finite matrix algebra $M_d(\mathbb{k})$ ($d \ge 1$) can realize
a central identity commutator $[J_1, J_{-1}] = 1$, establishing that affine Kac-Moody $[J_1, J_{-1}] = K$
and Virasoro $H^2(\mathcal{W}, \mathbb{Q}) \ne 0$ strictly require infinite mode rank. -/
theorem finite_matrix_no_central_identity_commutator
    (d : ℕ) [NeZero d] (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :
    ¬ ∃ Jp Jm : Matrix (Fin d) (Fin d) 𝕜, Jp * Jm - Jm * Jp = 1 := by
  rintro ⟨Jp, Jm, hcomm⟩
  have htr0 : Matrix.trace (Jp * Jm - Jm * Jp) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [hcomm, Matrix.trace_one, Fintype.card_fin] at htr0
  exact Nat.cast_ne_zero.mpr (NeZero.ne d) htr0

/-- Parameterized single-generation gravitational-hypercharge anomaly polynomial in $(N_c, Y_Q)$. -/
def gravHyperchargeAnomalyParam (Nc YQ : ℚ) : ℚ :=
  Nc * (2 * YQ - (YQ + 1 / 2) - (YQ - 1 / 2)) + (2 * (-1 / 2) - (-1))

/-- Parameterized single-generation $SU(2)_L^2 U(1)_Y$ mixed anomaly polynomial in $(N_c, Y_Q)$. -/
def su2MixedAnomalyParam (Nc YQ : ℚ) : ℚ :=
  2 * Nc * YQ + 2 * (-1 / 2)

/-- Parameterized single-generation $U(1)_Y^3$ cubic anomaly polynomial in $(N_c, Y_Q)$. -/
def u1CubicAnomalyParam (Nc YQ : ℚ) : ℚ :=
  Nc * (2 * YQ ^ 3 - (YQ + 1 / 2) ^ 3 - (YQ - 1 / 2) ^ 3) + (2 * (-1 / 2) ^ 3 - (-1) ^ 3)

/-- **Deduction 4 (Parameter-Honest Chiral Hypercharge-Color Reciprocity Law $N_c Y_Q = 1/2$)**:
Within a single chiral generation with normalized lepton hypercharges ($Y_L = -1/2$, $Y_e = -1$)
and weak-isospin splitting ($Y_{u,d} = Y_Q \pm 1/2$), gravitational cancellation holds for all $(N_c, Y_Q)$,
while $SU(2)_L^2 U(1)_Y = 0$ and $U(1)_Y^3 = 0$ hold iff $N_c Y_Q = 1/2$ (selecting $N_c = 3 \iff Y_Q = 1/6$). -/
theorem chiral_hypercharge_color_reciprocity (Nc YQ : ℚ) :
    gravHyperchargeAnomalyParam Nc YQ = 0 ∧
    (su2MixedAnomalyParam Nc YQ = 0 ∧ u1CubicAnomalyParam Nc YQ = 0 ↔ Nc * YQ = 1 / 2) ∧
    (su2MixedAnomalyParam Nc YQ = 0 ∧ u1CubicAnomalyParam Nc YQ = 0 → (Nc = 3 ↔ YQ = 1 / 6)) := by
  refine ⟨by unfold gravHyperchargeAnomalyParam; ring, ?_, ?_⟩
  · unfold su2MixedAnomalyParam u1CubicAnomalyParam
    constructor
    · rintro ⟨h1, _⟩; linarith
    · intro h
      have hcubic : Nc * (2 * YQ ^ 3 - (YQ + 1 / 2) ^ 3 - (YQ - 1 / 2) ^ 3) +
          (2 * (-1 / 2) ^ 3 - (-1) ^ 3) = (3 / 4 : ℚ) * (1 - 2 * (Nc * YQ)) := by ring
      rw [hcubic, h]
      exact ⟨by linarith, by norm_num⟩
  · rintro ⟨h1, _⟩
    unfold su2MixedAnomalyParam at h1
    constructor
    · rintro rfl; linarith
    · rintro rfl; linarith

/-- **Bost-Connes Regular ($\beta > 1$) vs. Critical ($\beta = 1$) Pole Dichotomy**:
Separates the regular convergent regime $\beta > 1$ ($Z(\beta) > 0$, $L \nearrow \mu(\beta) = \zeta(\beta)^{-1}$)
from the critical pole $\beta = 1$ (`¬ Summable (bc_eigenvalues 1)`) and the $\beta \to 1^+$ Souriau Fisher blow-up. -/
theorem bost_connes_regular_vs_critical_pole_dichotomy :
    (∀ β : ℝ, (hβ : 1 < β) →
      Summable (fun n : ℕ => (n : ℝ) ^ (-β)) ∧
      0 < SouriauBostConnesTransition.dirichletSeriesBC β hβ ∧
      L ↗ArithmeticFunction.moebius (β : ℂ) = (riemannZeta (β : ℂ))⁻¹) ∧
    ¬ Summable (InfoGeometry.Arithmetic.BostConnesCriticality.bc_eigenvalues 1) ∧
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β))
      (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
  refine ⟨?_,
    InfoGeometry.Arithmetic.BostConnesCriticality.operator_not_trace_class_at_critical,
    SouriauBostConnesTransition.tendsto_souriau_fisher_blowup⟩
  intro β hβ
  exact ⟨(SouriauBostConnesTransition.dirichletSeriesBC_hasSum β hβ).summable,
         SouriauBostConnesTransition.dirichletSeriesBC_pos β hβ,
         SouriauBostConnesTransition.bostConnes_witten_index_eq_reciprocal_zeta β hβ⟩

/-! ### Neutral Bott-0 $\mathrm{Cl}(4,4) \cong M_{16}(\mathbb{R})$ Krein Carrier, Witt $294 > 256$ Ceiling, & $\mathfrak{g}_{2(2)}$ Bridge -/

/-- 16-dimensional 4-qubit spinor index for the neutral Bott-0 Clifford algebra $\mathrm{Cl}(4,4) \cong M_{16}(\mathbb{R})$. -/
abbrev Krein16Idx := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- Fourfold Kronecker tensor product of $2 \times 2$ real matrices onto `Krein16Idx`. -/
def tensor4 (A B C D : Matrix (Fin 2) (Fin 2) ℝ) : Matrix Krein16Idx Krein16Idx ℝ :=
  Matrix.of fun (i₁, i₂, i₃, i₄) (j₁, j₂, j₃, j₄) =>
    A i₁ j₁ * B i₂ j₂ * C i₃ j₃ * D i₄ j₄

lemma tensor4_mul (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A₁ B₁ C₁ D₁ * tensor4 A₂ B₂ C₂ D₂ =
      tensor4 (A₁ * A₂) (B₁ * B₂) (C₁ * C₂) (D₁ * D₂) := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩
  simp only [tensor4, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

lemma tensor4_transpose (A B C D : Matrix (Fin 2) (Fin 2) ℝ) :
    (tensor4 A B C D)ᵀ = tensor4 Aᵀ Bᵀ Cᵀ Dᵀ := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩
  rfl

@[simp] lemma tensor4_neg_1 (A B C D : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 (-A) B C D = -tensor4 A B C D := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩; simp [tensor4]

@[simp] lemma tensor4_neg_2 (A B C D : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A (-B) C D = -tensor4 A B C D := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩; simp [tensor4]

@[simp] lemma tensor4_neg_3 (A B C D : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A B (-C) D = -tensor4 A B C D := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩; simp [tensor4]

@[simp] lemma tensor4_neg_4 (A B C D : Matrix (Fin 2) (Fin 2) ℝ) :
    tensor4 A B C (-D) = -tensor4 A B C D := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩; simp [tensor4]

lemma tensor4_one :
    tensor4 1 1 1 1 = (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
  ext ⟨i₁, i₂, i₃, i₄⟩ ⟨j₁, j₂, j₃, j₄⟩
  simp only [tensor4, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;>
    by_cases h3 : i₃ = j₃ <;> by_cases h4 : i₄ = j₄ <;>
    simp [h1, h2, h3, h4]

lemma tensor4_trace (A B C D : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (tensor4 A B C D) =
      Matrix.trace A * Matrix.trace B * Matrix.trace C * Matrix.trace D := by
  simp only [Matrix.trace, Matrix.diag, tensor4, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

@[simp] private lemma pinMinusGen_mul_self : pinMinusGen * pinMinusGen = 1 :=
  pin_clifford_reflection_parity_anomaly.1
@[simp] private lemma pinPlusGen_mul_self : pinPlusGen * pinPlusGen = -1 :=
  pin_clifford_reflection_parity_anomaly.2.1
@[simp] private lemma pinChiralGrading_mul_self : pinChiralGrading * pinChiralGrading = 1 :=
  pin_clifford_reflection_parity_anomaly.2.2.2.2.1
@[simp] private lemma pinMinusGen_mul_plus : pinMinusGen * pinPlusGen = pinChiralGrading :=
  pin_clifford_reflection_parity_anomaly.2.2.1
@[simp] private lemma pinPlusGen_mul_minus : pinPlusGen * pinMinusGen = -pinChiralGrading := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinPlusGen, pinMinusGen, pinChiralGrading, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] private lemma pinMinusGen_mul_grad : pinMinusGen * pinChiralGrading = pinPlusGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinMinusGen, pinChiralGrading, pinPlusGen, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] private lemma pinGrad_mul_minus : pinChiralGrading * pinMinusGen = -pinPlusGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinMinusGen, pinChiralGrading, pinPlusGen, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] private lemma pinPlusGen_mul_grad : pinPlusGen * pinChiralGrading = pinMinusGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinMinusGen, pinChiralGrading, pinPlusGen, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] private lemma pinGrad_mul_plus : pinChiralGrading * pinPlusGen = -pinMinusGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinMinusGen, pinChiralGrading, pinPlusGen, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] private lemma pinMinusGen_tr : pinMinusGenᵀ = pinMinusGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinMinusGen]
@[simp] private lemma pinPlusGen_tr : pinPlusGenᵀ = -pinPlusGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinPlusGen]
@[simp] private lemma pinChiralGrading_tr : pinChiralGradingᵀ = pinChiralGrading := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pinChiralGrading]

/-- Eight real Jordan-Wigner Clifford generators of $\mathrm{Cl}(4,4)$ on `Krein16Idx`. -/
def cl44Gen : Fin 8 → Matrix Krein16Idx Krein16Idx ℝ
  | 0 => tensor4 pinMinusGen 1 1 1
  | 1 => tensor4 pinChiralGrading pinMinusGen 1 1
  | 2 => tensor4 pinChiralGrading pinChiralGrading pinMinusGen 1
  | 3 => tensor4 pinChiralGrading pinChiralGrading pinChiralGrading pinMinusGen
  | 4 => tensor4 pinPlusGen 1 1 1
  | 5 => tensor4 pinChiralGrading pinPlusGen 1 1
  | 6 => tensor4 pinChiralGrading pinChiralGrading pinPlusGen 1
  | 7 => tensor4 pinChiralGrading pinChiralGrading pinChiralGrading pinPlusGen

/-- Chiral Majorana-Weyl volume involution $\Gamma_{4,4}$ on $\mathbb{R}^{16}$. -/
def gamma44 : Matrix Krein16Idx Krein16Idx ℝ :=
  tensor4 pinChiralGrading pinChiralGrading pinChiralGrading pinChiralGrading

/-- Double-real $(8,8)$ Krein fundamental symmetry $\widehat{\eta}_{8,8} = \tilde{e}_0 \tilde{e}_1 \tilde{e}_2 \tilde{e}_3$. -/
def kreinMetric88 : Matrix Krein16Idx Krein16Idx ℝ :=
  cl44Gen 4 * cl44Gen 5 * cl44Gen 6 * cl44Gen 7

/-- Explicit non-commutativity witness for `Matrix Krein16Idx Krein16Idx ℝ`. -/
theorem cl44Gen0_cl44Gen1_not_commute :
    cl44Gen 0 * cl44Gen 1 ≠ cl44Gen 1 * cl44Gen 0 := by
  intro h
  have h1 : cl44Gen 0 * cl44Gen 1 = tensor4 pinPlusGen pinMinusGen 1 1 := by
    dsimp [cl44Gen]; rw [tensor4_mul]; simp
  have h2 : cl44Gen 1 * cl44Gen 0 = -tensor4 pinPlusGen pinMinusGen 1 1 := by
    dsimp [cl44Gen]; rw [tensor4_mul]; simp
  rw [h1, h2] at h
  have hentry := congrFun (congrFun h (0, 0, 0, 0)) (1, 1, 0, 0)
  simp [tensor4, pinPlusGen, pinMinusGen] at hentry
  norm_num at hentry

/-- **Neutral Bott-0 $\mathrm{Cl}(4,4)$ Double-Real Krein Spinor & Bivector Skewness Theorem**:
Verifies $e_i^2 = +1$, $\tilde{e}_i^2 = -1$, $\{e_a, e_b\} = 0$ ($a \ne b$), $\Gamma_{4,4}^2 = 1$,
$\operatorname{Tr}(\Gamma_{4,4}) = 0$, $\widehat{\eta}_{8,8}^\top = \widehat{\eta}_{8,8}$, $\widehat{\eta}_{8,8}^2 = 1$,
$\operatorname{Tr}(\widehat{\eta}_{8,8}) = 0$, vector Krein-self-adjointness, and bivector Krein-skewness. -/
theorem cl44_krein_clifford_and_bivector_skewness :
    (∀ i : Fin 4, cl44Gen ⟨i.val, by omega⟩ * cl44Gen ⟨i.val, by omega⟩ = 1) ∧
    (∀ i : Fin 4, cl44Gen ⟨i.val + 4, by omega⟩ * cl44Gen ⟨i.val + 4, by omega⟩ = -1) ∧
    (∀ a b : Fin 8, a ≠ b → cl44Gen a * cl44Gen b + cl44Gen b * cl44Gen a = 0) ∧
    gamma44 * gamma44 = 1 ∧
    Matrix.trace gamma44 = 0 ∧
    kreinMetric88ᵀ = kreinMetric88 ∧
    kreinMetric88 * kreinMetric88 = 1 ∧
    Matrix.trace kreinMetric88 = 0 ∧
    (∀ a : Fin 8, kreinMetric88 * (cl44Gen a)ᵀ * kreinMetric88 = cl44Gen a) ∧
    (∀ a b : Fin 8, a ≠ b →
      kreinMetric88 * (cl44Gen a * cl44Gen b)ᵀ * kreinMetric88 = -(cl44Gen a * cl44Gen b)) := by
  have hEta : kreinMetric88 = tensor4 pinMinusGen pinPlusGen pinMinusGen pinPlusGen := by
    dsimp [kreinMetric88, cl44Gen]
    rw [tensor4_mul, tensor4_mul, tensor4_mul]
    simp
  have hEtaSq : kreinMetric88 * kreinMetric88 = 1 := by
    rw [hEta, tensor4_mul]
    simp [tensor4_one]
  have hAnticomm : ∀ a b : Fin 8, a ≠ b → cl44Gen a * cl44Gen b + cl44Gen b * cl44Gen a = 0 := by
    intro a b hab
    fin_cases a <;> fin_cases b
    any_goals contradiction
    all_goals
      dsimp [cl44Gen]
      rw [tensor4_mul, tensor4_mul]
      simp
  have hVecSym : ∀ a : Fin 8, kreinMetric88 * (cl44Gen a)ᵀ * kreinMetric88 = cl44Gen a := by
    intro a
    rw [hEta]
    fin_cases a <;>
      { dsimp [cl44Gen]
        rw [tensor4_transpose, tensor4_mul, tensor4_mul]
        simp }
  refine ⟨?_, ?_, hAnticomm, ?_, ?_, ?_, hEtaSq, ?_, hVecSym, ?_⟩
  · intro i
    fin_cases i <;> { dsimp [cl44Gen]; rw [tensor4_mul]; simp [tensor4_one] }
  · intro i
    fin_cases i <;> { dsimp [cl44Gen]; rw [tensor4_mul]; simp [tensor4_one] }
  · dsimp [gamma44]; rw [tensor4_mul]; simp [tensor4_one]
  · dsimp [gamma44]; rw [tensor4_trace]
    have htr : Matrix.trace pinChiralGrading = 0 := by
      simp [pinChiralGrading, Matrix.trace, Fin.sum_univ_two]
    rw [htr]; ring
  · rw [hEta, tensor4_transpose]; simp
  · rw [hEta, tensor4_trace]
    have htrP : Matrix.trace pinMinusGen = 0 := by
      simp [pinMinusGen, Matrix.trace, Fin.sum_univ_two]
    rw [htrP]; ring
  · intro a b hab
    have hba : cl44Gen b * cl44Gen a = -(cl44Gen a * cl44Gen b) :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hAnticomm a b hab)
    calc kreinMetric88 * (cl44Gen a * cl44Gen b)ᵀ * kreinMetric88
        = (kreinMetric88 * (cl44Gen b)ᵀ * kreinMetric88) *
          (kreinMetric88 * (cl44Gen a)ᵀ * kreinMetric88) := by
          rw [Matrix.transpose_mul]
          calc kreinMetric88 * ((cl44Gen b)ᵀ * (cl44Gen a)ᵀ) * kreinMetric88
              = kreinMetric88 * (cl44Gen b)ᵀ * (kreinMetric88 * kreinMetric88) *
                (cl44Gen a)ᵀ * kreinMetric88 := by rw [hEtaSq]; noncomm_ring
            _ = (kreinMetric88 * (cl44Gen b)ᵀ * kreinMetric88) *
                (kreinMetric88 * (cl44Gen a)ᵀ * kreinMetric88) := by noncomm_ring
      _ = cl44Gen b * cl44Gen a := by rw [hVecSym b, hVecSym a]
      _ = -(cl44Gen a * cl44Gen b) := hba

/-- Witt necklace dimension formula $W(r, n) = \frac{1}{n} \sum_{d \mid n} \mu(d) r^{n/d}$ for free Lie algebras. -/
def wittFreeLieDim (r n : ℕ) : ℤ :=
  (Finset.sum n.divisors fun d => ArithmeticFunction.moebius d * (r : ℤ) ^ (n / d)) / (n : ℤ)

/-- **Witt $294 > 256$ Rank-Ceiling, Non-Associative Leibniz Defect, Octonion Matrix Obstruction, & 14-Dim $\mathfrak{g}_{2(2)}$ Bridge**:
Wires `NonAssocIteratedLeibniz`, `OctonionMatrixObstruction`, and `CanonicalZornDerivationDimension`
to the $\mathrm{Cl}(4,4) \cong M_{16}(\mathbb{R})$ spinor ceiling. -/
theorem witt_free_lie_exceeds_cl44_matrix_ceiling :
    (Finset.sum (Finset.Icc 1 5) fun k => wittFreeLieDim 4 k) = 294 ∧
    Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) = 256 ∧
    (¬ ∃ fLin : (Fin 294 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ, Function.Injective fLin) ∧
    (∀ A B C : Matrix Krein16Idx Krein16Idx ℝ,
      (A * B - B * A) * C - C * (A * B - B * A) +
      ((B * C - C * B) * A - A * (B * C - C * B)) +
      ((C * A - A * C) * B - B * (C * A - A * C)) = 0) ∧
    (∀ {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
      (mul : A →ₗ[R] A →ₗ[R] A) (D : A →ₗ[R] A),
      InfoGeometry.Algebra.NonAssocIteratedLeibniz.IsDerivation mul D →
      ∀ x y : A, D (D (mul x y)) - mul (D (D x)) y - mul x (D (D y)) = (2 : R) • mul (D x) (D y)) ∧
    (¬ ∃ φ : InfoGeometry.Algebra.ZornMatrix ℝ → Matrix Krein16Idx Krein16Idx ℝ,
        Function.Injective φ ∧
        (∀ x y : InfoGeometry.Algebra.ZornMatrix ℝ, φ (x * y) = φ x * φ y)) ∧
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 := by
  have hfin256 : Module.finrank ℝ (Matrix Krein16Idx Krein16Idx ℝ) = 256 := by
    rw [Module.finrank_matrix, Module.finrank_self]
    decide
  have hwitt : (Finset.sum (Finset.Icc 1 5) fun k => wittFreeLieDim 4 k) = 294 := by
    have hIcc : Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
    have hd1 : (1 : ℕ).divisors = {1} := by decide
    have hd2 : (2 : ℕ).divisors = {1, 2} := by decide
    have hd3 : (3 : ℕ).divisors = {1, 3} := by decide
    have hd4 : (4 : ℕ).divisors = {1, 2, 4} := by decide
    have hd5 : (5 : ℕ).divisors = {1, 5} := by decide
    have hm2 : ArithmeticFunction.moebius 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
    have hm3 : ArithmeticFunction.moebius 3 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
    have hm4 : ArithmeticFunction.moebius 4 = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h => absurd (h 2 (by norm_num)) (by norm_num))
    have hm5 : ArithmeticFunction.moebius 5 = -1 := ArithmeticFunction.moebius_apply_prime (by norm_num)
    rw [hIcc]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton, wittFreeLieDim,
      hd1, hd2, hd3, hd4, hd5, ArithmeticFunction.moebius_apply_one, hm2, hm3, hm4, hm5]
    norm_num
  refine ⟨hwitt, hfin256, ?_, fun A B C => by noncomm_ring, ?_,
    InfoGeometry.Algebra.no_injective_matrix_representation_of_zornMatrix,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_canonicalZornDerivations⟩
  · rintro ⟨fLin, hL⟩
    have hle := LinearMap.finrank_le_finrank_of_injective hL
    rw [Module.finrank_fin_fun, hfin256] at hle
    omega
  · intro R A _ _ _ mul D hD x y
    have h2 := InfoGeometry.Algebra.NonAssocIteratedLeibniz.iterated_leibniz_smul mul D hD 2 x y
    simp [Finset.sum_range_succ, InfoGeometry.Algebra.NonAssocIteratedLeibniz.iterD] at h2
    change D (D (mul x y)) = mul x (D (D y)) + (2 : R) • mul (D x) (D y) + mul (D (D x)) y at h2
    rw [h2]
    abel

/-! ### `Type`-Level Five-Stage Data-Carrying Functorial Spine & 15-Node `COAGULA` Causal Poset -/

/-- Pure computational Stage I oblique Peirce corner extraction $N_+ = P X (1 - P)$. -/
def obliqueCorner {B : Type*} [Ring B] (P X : B) : B := P * X * (1 - P)

/-- Pure computational `Type`-valued Stage II deformed $\mathrm{Cl}(1,1)$ operator tuple. -/
structure PeirceCl11Frame (B : Type*) where
  phi : B
  jOp : B
  sigma : B
  metricV : B
  gradingS : B

/-- Stage I → Stage II functorial constructor feeding `Np` and dual `Y` into `PeirceCl11Frame`. -/
def buildPeirceCl11Frame {B : Type*} [Ring B] (P Np Y : B) : PeirceCl11Frame B :=
  let Nm := (1 - P) * Y * P
  { phi := Np + Nm
    jOp := Np - Nm
    sigma := Np * Nm - Nm * Np
    metricV := Np * Nm + Nm * Np
    gradingS := 2 * P - 1 }

/-- Explicit non-commutativity of `Type`-level operator transformations $F \circ G \ne G \circ F$,
contrasted with propositional conjunction symmetry $(P \wedge Q) \leftrightarrow (Q \wedge P)$. -/
theorem functorial_composition_noncomm_vs_prop_symm :
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let F : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun X => obliqueCorner P0 X
    let G : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun X => Xᵀ
    F ∘ G ≠ G ∘ F ∧ (∀ P Q : Prop, (P ∧ Q) ↔ (Q ∧ P)) := by
  dsimp
  refine ⟨?_, fun P Q => and_comm⟩
  intro h
  have hmat := congrFun h !![0, 0; (1 : ℂ), 0]
  have hentry := congrFun (congrFun hmat 0) 1
  simp [Function.comp, obliqueCorner, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at hentry

/-- **Five-Stage Data-Carrying Functorial Spine Theorem (`Ded.2` + `Ded.5`)**: -/
theorem five_stage_functorial_anomaly_spine
    {B : Type*} [Ring B] (P X Y : B) (hP : P * P = P)
    (Nc YQ : ℚ) (hRecip : Nc * YQ = 1 / 2) :
    let Np := obliqueCorner P X
    let F := buildPeirceCl11Frame P Np Y
    ((P + Np) * (P + Np) = P + Np ∧ (P + Np) * P - P * (P + Np) = -Np) ∧
    (F.phi * F.phi = F.metricV ∧
     F.jOp * F.jOp = -F.metricV ∧
     F.gradingS * (F.phi * F.jOp - F.jOp * F.phi) = -2 * F.metricV) ∧
    (gravHyperchargeAnomalyParam Nc YQ = 0 ∧
     su2MixedAnomalyParam Nc YQ = 0 ∧
     u1CubicAnomalyParam Nc YQ = 0) := by
  refine ⟨obliquePerturbation_idem_and_commutator P X hP, ?_, ?_⟩
  · have hCl := peirce_deformed_cl11_and_jordan_associator P X Y hP
    have hBr := grand_bridge_9 B P hP X Y
    exact ⟨hCl.1, hCl.2.1, hBr.1⟩
  · have hRec := chiral_hypercharge_color_reciprocity Nc YQ
    exact ⟨hRec.1, (hRec.2.1.mpr hRecip).1, (hRec.2.1.mpr hRecip).2⟩

/-- 15-element graded causal poset $\mathfrak{P}$ of `SOLVE-COAGULA` archetypes (`Grades 0..6`). -/
inductive AnomalyCoagulaNode : Type
  | Delta0_Cut
  | T_Thesis
  | S_Shadow
  | K_TT
  | Pi_ST
  | Sigma_TS
  | Gamma_SS
  | G_Gravity
  | Tau_Tension
  | A0_Defect
  | B_Spine
  | Aomega_Colimit
  | H_Holonomy
  | Cfun_Complex
  | XiTop_Synthesis
  deriving DecidableEq, Repr, Inhabited

namespace AnomalyCoagulaNode

/-- Strict causal grade $\mathrm{rk} : \mathfrak{P} \to \{0, \dots, 6\}$. -/
def rk : AnomalyCoagulaNode → ℕ
  | .Delta0_Cut      => 0
  | .T_Thesis        => 1
  | .S_Shadow        => 1
  | .K_TT            => 2
  | .Pi_ST           => 2
  | .Sigma_TS        => 2
  | .Gamma_SS        => 2
  | .G_Gravity       => 3
  | .Tau_Tension     => 3
  | .A0_Defect       => 3
  | .B_Spine         => 4
  | .Aomega_Colimit  => 4
  | .H_Holonomy      => 5
  | .Cfun_Complex    => 5
  | .XiTop_Synthesis => 6

/-- Transitively reduced Hasse covering relation $u \lessdot v$ of $(\mathfrak{P}, \prec)$. -/
def coversBool : AnomalyCoagulaNode → AnomalyCoagulaNode → Bool
  | .Delta0_Cut, .T_Thesis          => true
  | .Delta0_Cut, .S_Shadow          => true
  | .T_Thesis, .K_TT                => true
  | .T_Thesis, .Pi_ST               => true
  | .T_Thesis, .Sigma_TS            => true
  | .S_Shadow, .Pi_ST               => true
  | .S_Shadow, .Sigma_TS            => true
  | .S_Shadow, .Gamma_SS            => true
  | .Pi_ST, .G_Gravity              => true
  | .Sigma_TS, .G_Gravity           => true
  | .Pi_ST, .Tau_Tension            => true
  | .Sigma_TS, .Tau_Tension         => true
  | .K_TT, .A0_Defect               => true
  | .Pi_ST, .A0_Defect              => true
  | .Sigma_TS, .A0_Defect           => true
  | .K_TT, .B_Spine                 => true
  | .G_Gravity, .B_Spine            => true
  | .Tau_Tension, .B_Spine          => true
  | .Gamma_SS, .B_Spine             => true
  | .A0_Defect, .Aomega_Colimit     => true
  | .Tau_Tension, .Aomega_Colimit   => true
  | .Gamma_SS, .Aomega_Colimit      => true
  | .B_Spine, .H_Holonomy           => true
  | .Aomega_Colimit, .H_Holonomy    => true
  | .B_Spine, .Cfun_Complex         => true
  | .Aomega_Colimit, .Cfun_Complex  => true
  | .H_Holonomy, .XiTop_Synthesis   => true
  | .Cfun_Complex, .XiTop_Synthesis => true
  | _, _                            => false

/-- Propositional covering predicate $u \lessdot v$. -/
def Covers (u v : AnomalyCoagulaNode) : Prop := coversBool u v = true

lemma covers_rk_lt {u v : AnomalyCoagulaNode} (h : Covers u v) : u.rk < v.rk := by
  cases u <;> cases v <;> first | decide | cases h

lemma covers_rk_le_add_two {u v : AnomalyCoagulaNode} (h : Covers u v) : v.rk ≤ u.rk + 2 := by
  cases u <;> cases v <;> first | decide | cases h

lemma transGen_covers_rk_lt {u v : AnomalyCoagulaNode}
    (h : Relation.TransGen Covers u v) : u.rk < v.rk := by
  induction h with
  | single h1 => exact covers_rk_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (covers_rk_lt h2)

/-- Strict acyclicity of the 15-node `COAGULA` causal poset. -/
theorem covers_strict_acyclic (u : AnomalyCoagulaNode) :
    ¬ Relation.TransGen Covers u u :=
  fun h => Nat.lt_irrefl u.rk (transGen_covers_rk_lt h)

private lemma no_cover_triangle {u₁ u₂ v : AnomalyCoagulaNode}
    (h1 : Covers u₁ v) (h2 : Covers u₂ v) (h12 : Covers u₁ u₂) : False := by
  have hfalse : (coversBool u₁ v && coversBool u₂ v && coversBool u₁ u₂) = false := by
    cases v <;> cases u₁ <;> cases u₂ <;> rfl
  change coversBool u₁ v = true at h1
  change coversBool u₂ v = true at h2
  change coversBool u₁ u₂ = true at h12
  rw [h1, h2, h12] at hfalse
  cases hfalse

/-- Minimal-covering antichain property: covering predecessors of any node are pairwise incomparable. -/
theorem covers_pred_antichain {u₁ u₂ v : AnomalyCoagulaNode}
    (h1 : Covers u₁ v) (h2 : Covers u₂ v) :
    ¬ Relation.TransGen Covers u₁ u₂ := by
  intro h12
  cases h12 with
  | single hstep => exact no_cover_triangle h1 h2 hstep
  | tail hw1 hw2 =>
      have hlt1 := transGen_covers_rk_lt hw1
      have hlt2 := covers_rk_lt hw2
      have hltv := covers_rk_lt h2
      have hle := covers_rk_le_add_two h1
      omega

instance instPartialOrder : PartialOrder AnomalyCoagulaNode where
  le u v := Relation.ReflTransGen Covers u v
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ h1 h2 := Relation.ReflTransGen.trans h1 h2
  le_antisymm u _ h1 h2 := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h1 with rfl | ht1
    · rfl
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h2 with rfl | ht2
      · rfl
      · exact False.elim (Nat.lt_irrefl u.rk
          (Nat.lt_trans (transGen_covers_rk_lt ht1) (transGen_covers_rk_lt ht2)))

/-- Universal bottom bound $\mathbf{\Delta}_0 \preceq v$. -/
theorem bot_le_all (v : AnomalyCoagulaNode) : Delta0_Cut ≤ v := by
  cases v with
  | Delta0_Cut => exact Relation.ReflTransGen.refl
  | T_Thesis => exact Relation.ReflTransGen.single rfl
  | S_Shadow => exact Relation.ReflTransGen.single rfl
  | K_TT => exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis)) rfl
  | Pi_ST => exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis)) rfl
  | Sigma_TS => exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis)) rfl
  | Gamma_SS => exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut S_Shadow)) rfl
  | G_Gravity =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
          (rfl : Covers T_Thesis Pi_ST)) rfl
  | Tau_Tension =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
          (rfl : Covers T_Thesis Pi_ST)) rfl
  | A0_Defect =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
          (rfl : Covers T_Thesis K_TT)) rfl
  | B_Spine =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
          (rfl : Covers T_Thesis K_TT)) rfl
  | Aomega_Colimit =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut S_Shadow))
          (rfl : Covers S_Shadow Gamma_SS)) rfl
  | H_Holonomy =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
            (rfl : Covers T_Thesis K_TT))
          (rfl : Covers K_TT B_Spine)) rfl
  | Cfun_Complex =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
            (rfl : Covers T_Thesis K_TT))
          (rfl : Covers K_TT B_Spine)) rfl
  | XiTop_Synthesis =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail
            (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Delta0_Cut T_Thesis))
              (rfl : Covers T_Thesis K_TT))
            (rfl : Covers K_TT B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl

/-- Universal top bound $v \preceq \mathbf{\Xi}_\top$. -/
theorem all_le_top (v : AnomalyCoagulaNode) : v ≤ XiTop_Synthesis := by
  cases v with
  | XiTop_Synthesis => exact Relation.ReflTransGen.refl
  | H_Holonomy => exact Relation.ReflTransGen.single rfl
  | Cfun_Complex => exact Relation.ReflTransGen.single rfl
  | B_Spine =>
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers B_Spine H_Holonomy)) rfl
  | Aomega_Colimit =>
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Aomega_Colimit H_Holonomy)) rfl
  | G_Gravity =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers G_Gravity B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | Tau_Tension =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Tau_Tension B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | A0_Defect =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers A0_Defect Aomega_Colimit))
          (rfl : Covers Aomega_Colimit H_Holonomy)) rfl
  | K_TT =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers K_TT B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | Gamma_SS =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Gamma_SS B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | Pi_ST =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Pi_ST G_Gravity))
            (rfl : Covers G_Gravity B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | Sigma_TS =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers Sigma_TS G_Gravity))
            (rfl : Covers G_Gravity B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | T_Thesis =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers T_Thesis K_TT))
            (rfl : Covers K_TT B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | S_Shadow =>
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (rfl : Covers S_Shadow Gamma_SS))
            (rfl : Covers Gamma_SS B_Spine))
          (rfl : Covers B_Spine H_Holonomy)) rfl
  | Delta0_Cut => exact bot_le_all XiTop_Synthesis

/-- **Master Terminal Join Theorem ($\mathbf{Thm.\top}: \mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{C}_{\text{fun}}$)**:
Proves that `XiTop_Synthesis` is the unique least upper bound of `H_Holonomy` and `Cfun_Complex`. -/
theorem xiTop_isLUB_holonomy_and_functorialComplex :
    IsLUB ({H_Holonomy, Cfun_Complex} : Set AnomalyCoagulaNode) XiTop_Synthesis := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.single rfl
    · exact Relation.ReflTransGen.single rfl
  · intro z hz
    have hHz : H_Holonomy ≤ z := hz (Or.inl rfl)
    have hCz : Cfun_Complex ≤ z := hz (Or.inr rfl)
    rcases Relation.ReflTransGen.cases_head hHz with rfl | ⟨w, hcov, hwz⟩
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hCz with hEq | hlt
      · cases hEq
      · exact False.elim (Nat.lt_irrefl 5 (transGen_covers_rk_lt hlt))
    · cases w <;> first | exact hwz | cases hcov

end AnomalyCoagulaNode


/-! ## Part VIII: Master Capstone Synthesis Archetype -/

/-- Master Grand Anomaly Synthesis Archetype certifying the complete ontology across all 9 Clades. -/
def grandAnomalyOntologyArchetype : TypedArchetype Unit .proved where
  name     := `grandAnomalyOntologyArchetype
  phase    := 3
  claim    := fun _ =>
    -- Ontological Semantic Coverage
    (∀ s : GrandAnomalySemanticSense,
      ∃ c : GrandAnomalyTaxonomicClade, c.semanticSense = s ∨ c.secondarySemanticSense = s) ∧
    -- Bridge 1: Oblique defect = BRST Q
    (GenericObliqueIdempotentAnomaly.E01 (R := ℂ) = brstQ2 ∧
      GenericObliqueIdempotentAnomaly.commutator
          (GenericObliqueIdempotentAnomaly.oblique (R := ℂ))
          GenericObliqueIdempotentAnomaly.leftProjector = -brstQ2) ∧
    -- Bridge 2: Spin parity anomaly [N, N*] = Sigma(N) = sigma_z
    (pauliZ2 * !![0, (1 : ℂ); 0, 0] - !![0, (1 : ℂ); 0, 0] * pauliZ2 =
      (2 : ℂ) • !![0, (1 : ℂ); 0, 0]) ∧
    -- Bridge 3 & 5B: Off-diagonal Peirce homotope nilpotency & Cantor branch-chirality trace vanishing
    ((∀ (B : Type) [Ring B] (P : B) (_hP : P * P = P) (C A Z : B),
      InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z *
        InfoGeometry.OperatorAlgebra.PeirceSpine.upperHomotopeBracket P C A Z = 0) ∧
      (∀ n : ℕ,
        InfoGeometry.Canonical.KMSTraceColimit.normalizedTrace (n + 1) (branchChirality n) = 0)) ∧
    -- Bridge 4: Ungraded tracial vanishing vs supertrace doubling
    (∀ (A B : Matrix (Fin 2) (Fin 2) ℂ),
      A 0 0 = 0 → A 1 1 = 0 → B 0 0 = 0 → B 1 1 = 0 →
      Matrix.trace (A * B - B * A) = 0 ∧
      Matrix.trace (pauliZ2 * (A * B - B * A)) = 2 * Matrix.trace (pauliZ2 * (A * B))) ∧
    -- Bridge 6: Analytic Witten eta-phase, Pin± owners, & chirality inversion
    ((∀ ν : ℤ, Complex.exp ((ν : ℂ) * (2 * ↑Real.pi * Complex.I) / 16) = 1 ↔ (ν : ZMod 16) = 0) ∧
      WittenParityAnomalyBridge.IsPinMinus (InfoGeometry.Krein.modular_j (E := ℝ)) ∧
      WittenParityAnomalyBridge.IsPinPlus (InfoGeometry.Krein.complex_i (E := ℝ)) ∧
      pinMinusGen * pinChiralGrading * pinMinusGen = -pinChiralGrading) ∧
    -- Bridge 7 & 5D Hodge Disambiguation: Bivectors vs 3-Associators
    ((∀ r : ℕ, Omega.CircleDimension.anomalyConnectedDim r 0 = Nat.choose r 2) ∧
      (∀ r : ℕ, 0 < r → (Nat.choose r 2 = r ↔ r = 3)) ∧
      (∀ r : ℕ, 3 ≤ r → (Nat.choose r 2 = Nat.choose r 3 ↔ r = 5))) ∧
    -- Bridge 8B: 10×10 so(5,5) 5-graded contact Heisenberg, O(5,5) T-duality, & Cl(5,5) Bott closure
    (so55Grade1P * so55Grade1Q - so55Grade1Q * so55Grade1P = so55CenterPlus2 ∧
      so55CenterMinus2 * so55CenterPlus2 - so55CenterPlus2 * so55CenterMinus2 = so55ContactEuler ∧
      so55Metric * so55CenterPlus2 * so55Metric = so55CenterMinus2 ∧
      O55BottAnomalyClosure.cl55_bott_anomaly_closure_achieved =
        SplitCliffordTensorBridge.splitCliffordTensorStepEquiv 4) ∧
    -- Bridge 9 & 9B: Chiral Einstein anomaly, spin frame dragging, & Kantor-Jordan associator
    (∀ (B : Type) [Ring B] (P : B) (_hP : P * P = P) (X Y : B),
      let N_plus := P * X * (1 - P)
      let N_minus := (1 - P) * Y * P
      let Phi := N_plus + N_minus
      let J := N_plus - N_minus
      let Sigma := N_plus * N_minus - N_minus * N_plus
      let V := N_plus * N_minus + N_minus * N_plus
      let S_P := 2 * P - 1
      S_P * (Phi * J - J * Phi) = -2 * V ∧
      (Sigma * Phi - Phi * Sigma) = 2 * (V * J) ∧
      jordanAssociator N_minus N_plus N_plus = 2 * (V * N_plus)) ∧
    -- Bridge 10B: Universal InnerProductSpace Robertson QGT bound & Spinor Bloch-Robertson inequality
    ((∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (A B : H →ₗ[ℂ] H)
        (_hA : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y))
        (_hB : ∀ x y : H, inner ℂ (B x) y = inner ℂ x (B y))
        (ψ : H) (a b : ℝ),
        (1 / 4 : ℝ) * ‖inner ℂ ψ (A (B ψ) - B (A ψ))‖ ^ 2 ≤
          ‖A ψ - (a : ℂ) • ψ‖ ^ 2 * ‖B ψ - (b : ℂ) • ψ‖ ^ 2) ∧
      (∀ z₀ z₁ : ℂ,
        Complex.normSq z₀ + Complex.normSq z₁ = 1 →
        (1 / 4 : ℝ) * (-2 * (Complex.normSq z₀ - Complex.normSq z₁)) ^ 2 ≤
          (1 - (2 * (starRingEnd ℂ z₀ * z₁).re) ^ 2) *
          (1 - (2 * (starRingEnd ℂ z₀ * z₁).im) ^ 2))) ∧
    -- Bridge 11 & 11B: Resonant affine current, Virasoro Jacobi 2-cocycle, non-coboundary, & Sugawara c = 1
    ((∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜],
      ⁅InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Jinf 𝕜 1,
        InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Jinf 𝕜 (-1)⁆ =
        (1 : 𝕜) • InfoGeometry.Canonical.SplitCliffordInfiniteCurrent.Kinf 𝕜) ∧
      (∀ m : ℤ, virasoroCocycle m (-m) = 0 ↔ m = -1 ∨ m = 0 ∨ m = 1) ∧
      (¬ ∃ f : ℤ → ℚ, virasoroCocycle = wittCoboundary f) ∧
      InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1) ∧
    -- Bridges 12, 13, 14: Infinite Hilbert boundary sewing, McKean-Singer/Witten zeta, & KMS crystallization
    ((∀ (B : ConcreteHilbertCommutation.H_lp ℝ →L[ℝ] ConcreteHilbertCommutation.H_lp ℝ),
        (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
            (B.comp (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) = B →
        inner ℝ ConcreteHilbertSewnAnomaly.canonicalCantorSewnState
            (((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp B)
              ConcreteHilbertSewnAnomaly.canonicalCantorSewnState) = 0) ∧
      (∀ (β : ℝ), 1 < β → L ↗ArithmeticFunction.moebius (β : ℂ) = (riemannZeta (β : ℂ))⁻¹) ∧
      Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 1)) ∧
    -- Bridge 15 & 15B: Omega Jordan nilpotence & injective BRST intertwiner
    (Omega.Folding.gaugeAnomalyMinusHalfMatrix.mulVec Omega.Folding.gaugeAnomalyMinusHalfEigenvector = 0 ∧
      Omega.Folding.gaugeAnomalyMinusHalfMatrix.mulVec Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector =
        Omega.Folding.gaugeAnomalyMinusHalfEigenvector ∧
      (Omega.Folding.gaugeAnomalyMinusHalfMatrix *
        Omega.Folding.gaugeAnomalyMinusHalfMatrix).mulVec
        Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector = 0 ∧
      Function.Injective (fun c : Fin 2 → ℚ =>
        c 0 • Omega.Folding.gaugeAnomalyMinusHalfEigenvector +
        c 1 • Omega.Folding.gaugeAnomalyMinusHalfGeneralizedVector)) ∧
    -- Bridge 16 & 17: POM rewriting cohomology, Omega determinant/quotient/Window-6 laws, & N_c = 3 cancellation
    ((∀ {W C A Q : Type} [AddGroup A] [AddGroup Q]
        (classOf : A → Q) (_hadd : ∀ x y, classOf (x + y) = classOf x + classOf y)
        (_hzero : classOf 0 = 0) (boundary : C → A) (anom anom' : W → A)
        (_hchange : ∀ w, ∃ c, anom' w = anom w + boundary c)
        (_hboundary : ∀ c, classOf (boundary c) = 0),
      ∀ w, classOf (anom w) = 0 ↔ classOf (anom' w) = 0) ∧
      Omega.CircleDimension.anomalyConnectedDim 4 0 = 6 ∧
      (∀ Nc : ℚ, su2MixedAnomaly Nc = 0 ∧ u1CubicAnomaly Nc = 0 ↔ Nc = 3) ∧
      (∀ (q : ℕ) (_hq : 2 ≤ q) (C1 Cq det1 detq : ℝ) (_hC1 : C1 = det1⁻¹) (_hCq : Cq = detq⁻¹),
        Real.log Cq - (q : ℝ) * Real.log C1 = -Real.log detq + (q : ℝ) * Real.log det1) ∧
      Omega.GU.window6ThreeFamilyZeroAnom) ∧
    -- SOLVE-COAGULA Forensic Reconciliation: Krein QGT counterexample, finite trace wall,
    -- Nc*YQ = 1/2 reciprocity, critical beta = 1 pole, Cl(4,4)/Witt/G2(2) ceiling, & Xi_top IsLUB
    (LinearMap.ker kreinRealForm2 = ⊥ ∧
      ¬ ((1 / 4 : ℝ) * ‖kreinInnerC2 ![1, 1]
          (((!![1, (0 : ℂ); 0, -1] * !![0, Complex.I; Complex.I, 0] -
             !![0, Complex.I; Complex.I, 0] * !![1, (0 : ℂ); 0, -1]).mulVec) ![1, 1])‖ ^ 2 ≤ 0) ∧
      (∀ (d : ℕ) [NeZero d], ¬ ∃ Jp Jm : Matrix (Fin d) (Fin d) ℚ, Jp * Jm - Jm * Jp = 1) ∧
      (∀ Nc YQ : ℚ, su2MixedAnomalyParam Nc YQ = 0 ∧ u1CubicAnomalyParam Nc YQ = 0 ↔ Nc * YQ = 1 / 2) ∧
      ¬ Summable (InfoGeometry.Arithmetic.BostConnesCriticality.bc_eigenvalues 1) ∧
      (¬ ∃ fLin : (Fin 294 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ, Function.Injective fLin) ∧
      Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 ∧
      IsLUB ({AnomalyCoagulaNode.H_Holonomy, AnomalyCoagulaNode.Cfun_Complex} : Set AnomalyCoagulaNode)
        AnomalyCoagulaNode.XiTop_Synthesis) ∧
    -- Grand Causal Acyclicity
    (∀ e : GrandAnomalyPhylogeneticEpoch, ¬ Relation.TransGen GrandCausalEdge e e)
  evidence := fun _ => ⟨
    GrandAnomalyTaxonomicClade.semanticSense_complete_coverage,
    grand_bridge_1,
    grand_bridge_2_commutator,
    ⟨fun _B _ _P hP C A Z => (grand_bridge_3 hP C A Z).2.2,
     fun n => normalizedTrace_branchChirality n⟩,
    fun A B hA0 hA1 hB0 hB1 => grand_bridge_4 A B hA0 hA1 hB0 hB1,
    ⟨witten_eta_phase_trivial_iff_mod16,
     WittenParityAnomalyBridge.modular_j_is_pin_minus (E := ℝ),
     WittenParityAnomalyBridge.complex_i_is_pin_plus (E := ℝ),
     pin_clifford_reflection_parity_anomaly.2.2.2.2.2⟩,
    ⟨fun r => (grand_bridge_7 r 0).1,
     torsion_bivector_vs_associator_disambiguation.1,
     torsion_bivector_vs_associator_disambiguation.2⟩,
    ⟨grand_bridge_8_so55_five_grading.2.2.2.2.2.2.1,
     grand_bridge_8_so55_five_grading.2.2.2.2.2.2.2.2.2.2.1,
     grand_bridge_8_so55_five_grading.2.2.2.2.2.2.2.2.2.2.2.2.1,
     O55BottAnomalyClosure.cl55_bott_anomaly_closure_achieved_eq_owner⟩,
    fun B _ P hP X Y =>
      ⟨(grand_bridge_9 B P hP X Y).1,
       (grand_bridge_9 B P hP X Y).2,
       (peirce_deformed_cl11_and_jordan_associator P X Y hP).2.2.2.2.2.2.2.1⟩,
    ⟨fun _H _ _ A B hA hB ψ a b => robertson_qgt_uncertainty_bound A B hA hB ψ a b,
     fun z₀ z₁ hNorm => ((spinor_bloch_qgt_robertson_defect z₀ z₁).2 hNorm).2⟩,
    ⟨fun 𝕜 _ _ =>
      VirasoroProject.Extensions.PrimeVirasoroSugawara.CurrentCurrentLevelOneEvidence.owner_level_one 𝕜,
     virasoro_cocycle_cohomology.2.2.1,
     virasoro_cocycle_cohomology.2.2.2.1,
     VirasoroProject.Extensions.PrimeVirasoroSugawara.heisenberg_sugawara_centralCharge_eq_one⟩,
    ⟨grand_bridge_12.2,
     fun β hβ => SouriauBostConnesTransition.bostConnes_witten_index_eq_reciprocal_zeta β hβ,
     grand_bridge_14.2⟩,
    ⟨grand_bridge_15.1, grand_bridge_15.2.1,
     omega_parry_brst_intertwiner.2.1, omega_parry_brst_intertwiner.2.2⟩,
    ⟨fun classOf hadd hzero boundary anom anom' hchange hboundary =>
      Omega.POM.paper_pom_anom_cohomology_class classOf hadd hzero boundary anom anom' hchange hboundary,
     grand_bridge_17.1,
     grand_bridge_17.2.2.2.1,
     Omega.Zeta.paper_finite_part_moment_anomaly_reduced_determinant_ratio,
     window6ThreeFamilyZeroAnom_pure⟩,
    ⟨krein_robertson_qgt_counterexample_and_null_cone_survival.1,
     krein_robertson_qgt_counterexample_and_null_cone_survival.2.2.2.2.2.2.2,
     fun d _ => finite_matrix_no_central_identity_commutator d ℚ,
     fun Nc YQ => (chiral_hypercharge_color_reciprocity Nc YQ).2.1,
     bost_connes_regular_vs_critical_pole_dichotomy.2.1,
     witt_free_lie_exceeds_cl44_matrix_ceiling.2.2.1,
     witt_free_lie_exceeds_cl44_matrix_ceiling.2.2.2.2.2.2,
     AnomalyCoagulaNode.xiTop_isLUB_holonomy_and_functorialComplex⟩,
    grandCausalEdge_acyclic
  ⟩

/-- `Type`-parameterized Functorial Spine Archetype acting on concrete operator pairs `(X, Y)`
in `Matrix (Fin 2) (Fin 2) ℂ` rather than `Unit`, certifying data-carrying Stage I → Stage II chaining. -/
def functorialSpineArchetype :
    TypedArchetype (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) .proved where
  name     := `functorialSpineArchetype
  phase    := 3
  claim    := fun XY =>
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let Np := obliqueCorner P0 XY.1
    let F := buildPeirceCl11Frame P0 Np XY.2
    ((P0 + Np) * (P0 + Np) = P0 + Np ∧ (P0 + Np) * P0 - P0 * (P0 + Np) = -Np) ∧
    (F.phi * F.phi = F.metricV ∧
     F.jOp * F.jOp = -F.metricV ∧
     F.gradingS * (F.phi * F.jOp - F.jOp * F.phi) = -2 * F.metricV)
  evidence := fun XY => by
    have hP0 : (!![1, (0 : ℂ); 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0] = !![1, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hSpine := five_stage_functorial_anomaly_spine !![1, (0 : ℂ); 0, 0] XY.1 XY.2 hP0 3 (1 / 6) (by norm_num)
    exact ⟨hSpine.1, hSpine.2.1⟩

#register_archetype functorialSpineArchetype
#audit_archetype functorialSpineArchetype

#register_archetype grandAnomalyOntologyArchetype
#audit_archetype grandAnomalyOntologyArchetype

end InfoGeometry.Canonical.GrandAnomalyOntology
