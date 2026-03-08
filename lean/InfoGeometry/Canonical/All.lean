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
import InfoGeometry.Canonical.AnalyticalIndex
import InfoGeometry.Canonical.AQFTOperatorInterface
import InfoGeometry.Canonical.OperatorAlgebraBridge
import InfoGeometry.Canonical.AnomalyGauge
import InfoGeometry.Canonical.AnomalyInflow
import InfoGeometry.Canonical.Attention
import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Canonical.BeliefAlgebra
import InfoGeometry.Canonical.BeliefDynamics
import InfoGeometry.Canonical.BerryPhase
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.BottPeriodicity
import InfoGeometry.Canonical.BregmanTriality
import InfoGeometry.Canonical.CalabiYauBridge
import InfoGeometry.Canonical.CartanDecomposition
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.ChiralAction
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.ChiralCliffordBridge
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.ChiralGravity
import InfoGeometry.Canonical.ChiralRGFlow
import InfoGeometry.Canonical.ChiralTorsionBridge
import InfoGeometry.Canonical.Clifford
import InfoGeometry.Canonical.CliffordBridge
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.ConformalWard
import InfoGeometry.Core
import InfoGeometry.Core.Derivatives
import InfoGeometry.Core.DerivativesSmoke
import InfoGeometry.Core.Jordan
import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Core.SymmetricLieGeneric
import InfoGeometry.Core.SymmetricSpaces
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Canonical.CountSubstrateBridge
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Canonical.DeepHorizon
import InfoGeometry.Canonical.DiracRicciBridge
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DualConnections
import InfoGeometry.Canonical.EmpiricalChecks
import InfoGeometry.Canonical.Fierz
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.Fock
import InfoGeometry.Canonical.Foundations
import InfoGeometry.Canonical.GaugeUnified
import InfoGeometry.Canonical.GaugeGroups
import InfoGeometry.Canonical.GaussianHolonomy
import InfoGeometry.Canonical.Geometry
import InfoGeometry.Canonical.GrandCanonicalCore
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.GrandUnificationBlueprint
import InfoGeometry.Canonical.GrandUnificationMetric
import InfoGeometry.Canonical.HeatKernel
import InfoGeometry.Canonical.HolographicEmergence
import InfoGeometry.Canonical.IB
import InfoGeometry.Canonical.InformationNumber
import InfoGeometry.Canonical.InformationTorsion
import InfoGeometry.Canonical.KKFoundation
import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.Canonical.SuperAnomaly
import InfoGeometry.KL.EntropicInferenceTest
import InfoGeometry.SLT.ConditionalExpectation
import InfoGeometry.TransformationGroups
import InfoGeometry.auto_blueprints
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.Krein
import InfoGeometry.Canonical.KreinLadder
import InfoGeometry.LLM
import InfoGeometry.LLM.MaskedTransformerBlock
import InfoGeometry.LLM.PositionalEncoding
import InfoGeometry.LLM.TransformerBlock
import InfoGeometry.Canonical.LLN
import InfoGeometry.Canonical.LorentzianRouting
import InfoGeometry.Canonical.ManifoldDegree
import InfoGeometry.Canonical.ManifoldHomology
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.LogDet
import InfoGeometry.Canonical.LogSumExp
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.PerelmanW
import InfoGeometry.Canonical.Prequantum
import InfoGeometry.Canonical.Projective
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.Quantum
import InfoGeometry.Canonical.QuantumInference
import InfoGeometry.Canonical.RGFlow
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.RedLine
import InfoGeometry.Canonical.Rosetta
import InfoGeometry.Canonical.SpectralInference
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
import InfoGeometry.Canonical.WeylInformationGauge
import InfoGeometry.Canonical.WilsonLoop
import InfoGeometry.Canonical.YangMillsBridge

/-!
# InfoGeometry.Canonical.All

Single canonical umbrella for all publishable InfoGeometry modules.
This default surface imports the canonical modules directly.

Documentation:
- [Cocycle Detailed-Balance Synthesis](docs/cocycle_detailed_balance_synthesis.md)
- [Determinant Tensor-Entropy Synthesis](docs/determinant_tensor_entropy_synthesis.md)
- [D4 Crystal Synthesis](docs/d4_crystal_synthesis.md)
- [Deep Horizon Synthesis](docs/deep_horizon_synthesis.md)
- [Drazin Conformal Synthesis](docs/drazin_conformal_synthesis.md)
- [Gravity Gauge Synthesis](docs/gravity_gauge_synthesis.md)
- [LLM Triality Synthesis](docs/llm_triality_synthesis.md)
- [Ontology Synthesis](docs/ontology_synthesis.md)
- [PRL Abstract/Intro Draft](docs/prl_abstract_intro_synthesis.md)
- [Red Line Synthesis](docs/red_line_synthesis.md)
- [Testable Physical Predictions](docs/testable_predictions.md)
- [Witten Synthesis](docs/witten_synthesis.md)
-/
