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

import InfoGeometry.Canonical.Algebra
import InfoGeometry.Canonical.AnalysisLegacy
import InfoGeometry.Canonical.AnalyticalIndex
import InfoGeometry.Canonical.AQFTOperatorInterface
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
import InfoGeometry.Canonical.CoreLegacy
import InfoGeometry.Canonical.CountSubstrateBridge
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DualConnections
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.Foundations
import InfoGeometry.Canonical.GaugeUnified
import InfoGeometry.Canonical.Geometry
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
import InfoGeometry.Canonical.IntegrationLegacy
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.Krein
import InfoGeometry.Canonical.KreinLadder
import InfoGeometry.Canonical.LLMLegacy
import InfoGeometry.Canonical.LLN
import InfoGeometry.Canonical.LorentzianRouting
import InfoGeometry.Canonical.ManifoldHomology
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.PerelmanW
import InfoGeometry.Canonical.Prequantum
import InfoGeometry.Canonical.Projective
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.Quantum
import InfoGeometry.Canonical.QuantumInference
import InfoGeometry.Canonical.RGFlow
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.Rosetta
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.Statistics
import InfoGeometry.Canonical.SuperInference
import InfoGeometry.Canonical.Thermo
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TopologicalEuler
import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.Twistor
import InfoGeometry.Canonical.WeylInformationGauge

/-!
# InfoGeometry.Canonical.All

Single canonical umbrella for all publishable InfoGeometry modules.
This default surface imports the canonical modules directly.
-/
