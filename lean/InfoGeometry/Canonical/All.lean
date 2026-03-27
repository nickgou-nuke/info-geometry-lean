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
import InfoGeometry.Canonical.AQFTOperatorInterface
import InfoGeometry.Canonical.AnomalyDilationBridge
import InfoGeometry.Canonical.AnomalyInflow
import InfoGeometry.Canonical.AnomalyGauge
import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Canonical.Attention
import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Canonical.AttentionPolarizedSplit
import InfoGeometry.Canonical.AttentionPolarizedGibbsBridge
import InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge
import InfoGeometry.Canonical.BerryPhase
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BogoliubovPolarizationBridge
import InfoGeometry.Canonical.KreinDiracPolarizationBridge
import InfoGeometry.Canonical.KreinDiracSpectralLift
import InfoGeometry.Canonical.SplitCliffordThermalBridge
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
import InfoGeometry.Canonical.OperatorialInformationLift
import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.BottPeriodicity
import InfoGeometry.Canonical.BregmanTriality
import InfoGeometry.Canonical.CartanDecomposition
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.ChiralAction
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.ChiralGravity
import InfoGeometry.Canonical.ChiralRGFlow
import InfoGeometry.Canonical.Clifford
import InfoGeometry.Canonical.CliffordBridge
import InfoGeometry.Canonical.ConformalWard
import InfoGeometry.Canonical.ConnesArakiFramework
import InfoGeometry.Canonical.CountSubstrateBridge
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Canonical.DeepHorizon
import InfoGeometry.Core
import InfoGeometry.Core.Derivatives
import InfoGeometry.Core.DerivativesSmoke
import InfoGeometry.Core.Jordan
import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Core.SymmetricLieGeneric
import InfoGeometry.Core.SymmetricSpaces
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.CoarseGraining
import InfoGeometry.Canonical.Determinant
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.LogGenerator
import InfoGeometry.Canonical.GeneratedFlow
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.WeylTransportChiralBridge
import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Canonical.PartitionHierarchy
import InfoGeometry.Canonical.DualConnections
import InfoGeometry.Canonical.EmpiricalChecks
import InfoGeometry.Canonical.Fierz
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.Fock
import InfoGeometry.Canonical.Foundations
import InfoGeometry.Canonical.GaugeUnified
import InfoGeometry.Canonical.GaugeGroups
import InfoGeometry.Canonical.GaussianHolonomy
import InfoGeometry.Canonical.GeneralizedKL
import InfoGeometry.Canonical.Geometry
import InfoGeometry.Canonical.GrandCanonicalCore
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.GrandUnificationBlueprint
import InfoGeometry.Canonical.GrandUnificationMetric
import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.HeatKernel
import InfoGeometry.Canonical.IB
import InfoGeometry.Canonical.InformationCalculus
import InfoGeometry.Canonical.InformationNumber
import InfoGeometry.Canonical.InformationTorsion
import InfoGeometry.Canonical.KKFoundation
import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.Canonical.SuperAnomaly
import InfoGeometry.KL.EntropicInferenceTest
import InfoGeometry.SLT.ConditionalExpectation
import InfoGeometry.TransformationGroups
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.Canonical.Krein
import InfoGeometry.Canonical.KreinLadder
import InfoGeometry.LLM
import InfoGeometry.LLM.MaskedTransformerBlock
import InfoGeometry.LLM.PositionalEncoding
import InfoGeometry.LLM.TransformerBlock
import InfoGeometry.Canonical.LLN
import InfoGeometry.Canonical.LogSpineBridge
import InfoGeometry.Canonical.LorentzianRouting
import InfoGeometry.Canonical.ManifoldDegree
import InfoGeometry.Canonical.ManifoldHomology
import InfoGeometry.Canonical.ManifoldDegreeIntegration
import InfoGeometry.Canonical.MasterSynthesis
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.ModularSpinorBridge
import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Canonical.NoetherInference
import InfoGeometry.Canonical.OperatorAlgebraBridge
import InfoGeometry.Canonical.PartitionHierarchy
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.Prequantum
import InfoGeometry.Canonical.Projective
import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Canonical.RobustThermodynamicRegression
import InfoGeometry.Canonical.Rosetta
import InfoGeometry.Canonical.Quantum
import InfoGeometry.Canonical.QuantumInference
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.RGFlow
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.RedLine
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.SingularBoundaryCorrection
import InfoGeometry.Canonical.CalabiYauSingularBridge
import InfoGeometry.Canonical.SingularTransportSystem
import InfoGeometry.Canonical.Statistics
import InfoGeometry.Canonical.SuperInference
import InfoGeometry.Canonical.SUSYBayes
import InfoGeometry.Canonical.Thermo
import InfoGeometry.Canonical.ThermoFromLogDet
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TopologicalEuler
import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.Twistor
import InfoGeometry.Canonical.Unification
import InfoGeometry.Canonical.WilsonLoop
import InfoGeometry.Canonical.YangMillsFinite
import InfoGeometry.PositiveMeasure
import InfoGeometry.Projective.Normalize
import InfoGeometry.Projective.TwistorBridge
import InfoGeometry.Quantum.BulkBoundaryIndexBridge
import InfoGeometry.Quantum.ModularAnomaly
import InfoGeometry.Volume.RadonNikodym
import InfoGeometry.Volume.LogPotential
import InfoGeometry.Volume.Pfaffian

/-!
# InfoGeometry.Canonical.All

Single umbrella import for the canonical publication surface.

This file is an import aggregator, not an authoritative description of the
current theory graph. For current repository state and workflow, prefer:
- `README.md`
- `docs/README.md`
- `lean/DAG/README.md`
- `tools/README.md`

Conceptual notes under `docs/` are orientation aids only. Exact ownership,
theorem names, and file boundaries must be checked against the current owner
modules in `lean/InfoGeometry/Canonical/`.
-/
