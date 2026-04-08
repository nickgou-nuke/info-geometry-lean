/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import DAG.Basic
import InfoGeometry.Canonical.Algebra
import InfoGeometry.Canonical.ActionDuality
import InfoGeometry.Canonical.AnomalyInflow
import InfoGeometry.Canonical.AnomalyGauge
import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Canonical.Attention
import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.BottPeriodicity
import InfoGeometry.Canonical.BregmanTriality
import InfoGeometry.Canonical.CartanDecomposition
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.ChiralGravity
import InfoGeometry.Canonical.ChiralRGFlow
import InfoGeometry.Canonical.Clifford
import InfoGeometry.Canonical.ClNNBottBridge
import InfoGeometry.Canonical.CliffordBridge
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Core
import InfoGeometry.Core.Derivatives
import InfoGeometry.Core.DerivativesSmoke
import InfoGeometry.Core.Jordan
import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Core.SymmetricLieGeneric
import InfoGeometry.Core.SymmetricSpaces
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.CoarseGraining
import InfoGeometry.Canonical.Determinant
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.DrazinDescriptorSystems
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.InverseKernelCartanCore
import InfoGeometry.Canonical.InverseKernelNormalForm
import InfoGeometry.Canonical.LogGenerator
import InfoGeometry.Canonical.GeneratedFlow
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.WeylTransportChiralBridge
import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Canonical.VolumeDeformationPrinciple
import InfoGeometry.Canonical.PartitionHierarchy
import InfoGeometry.Canonical.DualConnections
import InfoGeometry.Canonical.EmpiricalChecks
import InfoGeometry.Canonical.EPAndGroupInverse
import InfoGeometry.Canonical.EPDefectAlgebra
import InfoGeometry.Canonical.Fierz
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.Fock
import InfoGeometry.Canonical.Foundations
import InfoGeometry.Canonical.GaugeUnified
import InfoGeometry.Canonical.GaugeGroups
import InfoGeometry.Canonical.GaussianHolonomy
import InfoGeometry.Canonical.GeneralizedKL
import InfoGeometry.Canonical.GeneralizedMetricCore
import InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge
import InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
import InfoGeometry.Canonical.Geometry
import InfoGeometry.Canonical.GrandCanonicalCore
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.GrandUnificationMetric
import InfoGeometry.Canonical.HeatKernel
import InfoGeometry.Canonical.IB
import InfoGeometry.Canonical.InformationNumber
import InfoGeometry.Canonical.InformationTorsion
import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.KKTGeneralizedInverseBridge
import InfoGeometry.Canonical.KKTGeneralizedMetricBridge
import InfoGeometry.Canonical.KKFoundation
import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Canonical.SuperAnomaly
import InfoGeometry.KL.EntropicInferenceTest
import InfoGeometry.SLT.ConditionalExpectation
import InfoGeometry.TransformationGroups
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KreinDoubledAtom
import InfoGeometry.Canonical.KLinearRepresentation
import InfoGeometry.Canonical.PolarizedMadelungBridge
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Canonical.BogoliubovProjectorTransport
import InfoGeometry.Canonical.BogoliubovProjectorFlux
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.Canonical.Krein
import InfoGeometry.Canonical.KreinLadder
import InfoGeometry.LLM
import InfoGeometry.LLM.MaskedTransformerBlock
import InfoGeometry.LLM.TransformerBlock
import InfoGeometry.Canonical.LLN
import InfoGeometry.Canonical.LogSumExp
import InfoGeometry.Canonical.LogSpineBridge
import InfoGeometry.Canonical.LorentzianRouting
import InfoGeometry.Canonical.ManifoldDegree
import InfoGeometry.Canonical.ManifoldHomology
import InfoGeometry.Canonical.ManifoldDegreeIntegration
import InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.ModularSpinorBridge
import InfoGeometry.Canonical.NoetherInference
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.PhaseSpaceRecompositionExample
import InfoGeometry.Canonical.Prequantum
import InfoGeometry.Canonical.Projective
import InfoGeometry.Canonical.RelativeModularCore
import InfoGeometry.Canonical.RelativeModularPolarizedBridge
import InfoGeometry.Canonical.RelativeModularProjectiveBridge
import InfoGeometry.Canonical.RelativeModularRecomposition
import InfoGeometry.Canonical.RobustThermodynamicRegression
import InfoGeometry.Canonical.Quantum
import InfoGeometry.Canonical.QuantumInference
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.RGFlow
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Canonical.MongeAmpereDualSheetBridge
import InfoGeometry.Canonical.RestrictedSheetContinuous
import InfoGeometry.Canonical.RestrictedVolumeCharacter
import InfoGeometry.Canonical.WeylGaugeOperatorLift
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Canonical.RealBdGSheetBridge
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Canonical.SingularBoundaryCorrection
import InfoGeometry.Canonical.CalabiYauSingularBridge
import InfoGeometry.Canonical.SingularTransportSystem
import InfoGeometry.Canonical.Statistics
import InfoGeometry.Canonical.SuperInference
import InfoGeometry.Canonical.Thermo
import InfoGeometry.Canonical.ThermoFromLogDet
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TopologicalEuler
import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.Twistor
import InfoGeometry.Canonical.Unification
import InfoGeometry.PositiveMeasure
import InfoGeometry.Quantum.BulkBoundaryIndexBridge
import InfoGeometry.Canonical.BulkBoundaryRegularizationBridge
import InfoGeometry.Quantum.ModularAnomaly
import InfoGeometry.Quantum.TriadicTransportCore
import InfoGeometry.Quantum.TriadicTransportProjective
import InfoGeometry.Quantum.TriadicTransportBarycenter
import InfoGeometry.Quantum.TriadicTransportModular
import InfoGeometry.Quantum.TriadicBogoliubovBridge
import InfoGeometry.Quantum.TriadicWeylBridge
import InfoGeometry.Volume.RadonNikodym
import InfoGeometry.Volume.LogPotential
import InfoGeometry.Volume.Pfaffian

-- Stable declaration-bearing canonical owners previously outside the umbrella coverage.
import InfoGeometry.Canonical.AQFTHilbertCompression
import InfoGeometry.Canonical.AQFTOperatorEndpoints
import InfoGeometry.Canonical.AQFTOperatorSignatures
import InfoGeometry.Canonical.AQFTReadiness
import InfoGeometry.Canonical.BerryConnection
import InfoGeometry.Canonical.BeliefAlgebra
import InfoGeometry.Canonical.CartanBerezinianCore
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.CalabiYauWBridge
import InfoGeometry.Canonical.ChiralTorsionGeneralizedKL
import InfoGeometry.Canonical.ChiralTorsionState
import InfoGeometry.Canonical.ChiralTorsionTwistor
import InfoGeometry.Canonical.ConnesArakiCore
import InfoGeometry.Canonical.ConnesArakiTomita
import InfoGeometry.Canonical.CountPositiveCoupling
import InfoGeometry.Canonical.CountProbabilityState
import InfoGeometry.Canonical.CountSinkhornFlow
import InfoGeometry.Canonical.GrandSynthesisBott
import InfoGeometry.Canonical.GrandSynthesisGeometry
import InfoGeometry.Canonical.GrandSynthesisSingular
import InfoGeometry.Canonical.GrandSynthesisThermo
import InfoGeometry.Canonical.OperatorAlgebraAQFTPackage
import InfoGeometry.Canonical.OperatorAlgebraKKBridge
import InfoGeometry.Canonical.OperatorAlgebraModularAtom
import InfoGeometry.Canonical.OperatorAlgebraReadiness
import InfoGeometry.Canonical.ResponseWeylAnomalyBridge
import InfoGeometry.Canonical.RosettaScaleTransport
import InfoGeometry.Canonical.WeylPathHysteresis
import InfoGeometry.Canonical.YangMillsFiniteBridge
import InfoGeometry.Canonical.YangMillsFiniteQFT

-- Stable depth ladder for the count/projective/operator/Krein/transport/attention spine.
-- L0: count / relative-volume substrate
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.ModularVolumeDeformationBridge

-- L1: projective / gauge / scalar modular-potential layer
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Projective.Normalize

-- L2: diagonal operator lift and partition calculus
import InfoGeometry.Canonical.InformationPartitionCore
import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.RelativeModularSingularization
import InfoGeometry.Canonical.RelativeSurprisalOperatorLift

-- L3: spectral / metric coherence on the doubled carrier
import InfoGeometry.Canonical.DiagonalMetricModularBridge
import InfoGeometry.Canonical.RelativeModularBerezinianBridge
import InfoGeometry.Canonical.KreinDiracPolarizationBridge

-- L4: transported/Bogoliubov presentation
import InfoGeometry.Canonical.BogoliubovPolarizationBridge
import InfoGeometry.Canonical.KreinDiracSpectralLift
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
import InfoGeometry.Canonical.SplitCliffordThermalBridge
import InfoGeometry.Canonical.OperatorialInformationLift

-- L5: thermodynamic / attention surface
import InfoGeometry.Canonical.AttentionPolarizedSplit
import InfoGeometry.Canonical.AttentionPolarizedGibbsBridge
import InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge

/-!
# InfoGeometry.Canonical.All

Stable umbrella import for the canonical publication surface.

This file intentionally excludes modules listed in
`scripts/quality/quarantine_manifest.txt`. Quarantined synthesis/facade layers
must be imported explicitly from their owner modules while they remain on the
review surface.

This file is still only an import aggregator, not an authoritative description
of the current theory graph. For current repository state and workflow, prefer:
- `README.md`
- `docs/README.md`
- `lean/DAG/README.md`
- `tools/README.md`

Conceptual notes under `docs/` are orientation aids only. Exact ownership,
theorem names, and file boundaries must be checked against the current owner
modules in `lean/InfoGeometry/Canonical/`.
-/
