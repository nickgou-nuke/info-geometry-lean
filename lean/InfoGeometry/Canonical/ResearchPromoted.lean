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

import InfoGeometry.Canonical.Promoted.AnalyticalIndex
import InfoGeometry.Canonical.Promoted.AQFTOperatorInterface
import InfoGeometry.Canonical.Promoted.AnomalyInflow
import InfoGeometry.Canonical.Promoted.Attention
import InfoGeometry.Canonical.Promoted.AttentionEuclidean
import InfoGeometry.Canonical.Promoted.AttentionSplit
import InfoGeometry.Canonical.Promoted.BeliefAlgebra
import InfoGeometry.Canonical.Promoted.BeliefDynamics
import InfoGeometry.Canonical.Promoted.BerryPhase
import InfoGeometry.Canonical.Promoted.BogoliubovFockSuper
import InfoGeometry.Canonical.Promoted.BottDirac
import InfoGeometry.Canonical.Promoted.BottPeriodicity
import InfoGeometry.Canonical.Promoted.BregmanTriality
import InfoGeometry.Canonical.Promoted.CalabiYauBridge
import InfoGeometry.Canonical.Promoted.CartanDecomposition
import InfoGeometry.Canonical.Promoted.CayleyBregmanBridge
import InfoGeometry.Canonical.Promoted.ChiralAction
import InfoGeometry.Canonical.Promoted.ChiralAnomaly
import InfoGeometry.Canonical.Promoted.ChiralCliffordBridge
import InfoGeometry.Canonical.Promoted.ChiralEinsteinBridge
import InfoGeometry.Canonical.Promoted.ChiralGravity
import InfoGeometry.Canonical.Promoted.ChiralRGFlow
import InfoGeometry.Canonical.Promoted.ChiralTorsionBridge
import InfoGeometry.Canonical.Promoted.CliffordBridge
import InfoGeometry.Canonical.Promoted.ConformalAlgebra
import InfoGeometry.Canonical.Promoted.ConformalUnification
import InfoGeometry.Canonical.Promoted.ConformalWard
import InfoGeometry.Canonical.Promoted.CountSubstrateBridge
import InfoGeometry.Canonical.Promoted.CurvatureRGFlow
import InfoGeometry.Canonical.Promoted.Drazin
import InfoGeometry.Canonical.Promoted.DualConnections
import InfoGeometry.Canonical.Promoted.FormalScaffold
import InfoGeometry.Canonical.Promoted.GaugeUnified
import InfoGeometry.Canonical.Promoted.GrandCanonicalExperts
import InfoGeometry.Canonical.Promoted.GrandSynthesis
import InfoGeometry.Canonical.Promoted.GrandUnification
import InfoGeometry.Canonical.Promoted.GrandUnificationBlueprint
import InfoGeometry.Canonical.Promoted.GrandUnificationMetric
import InfoGeometry.Canonical.Promoted.HeatKernel
import InfoGeometry.Canonical.Promoted.HolographicEmergence
import InfoGeometry.Canonical.Promoted.IB
import InfoGeometry.Canonical.Promoted.InformationNumber
import InfoGeometry.Canonical.Promoted.InformationTorsion
import InfoGeometry.Canonical.Promoted.KMSSinkhornBridge
import InfoGeometry.Canonical.Promoted.KaehlerGeometry
import InfoGeometry.Canonical.Promoted.KreinLadder
import InfoGeometry.Canonical.Promoted.LLN
import InfoGeometry.Canonical.Promoted.LorentzianRouting
import InfoGeometry.Canonical.Promoted.ManifoldHomology
import InfoGeometry.Canonical.Promoted.MixtureOfExperts
import InfoGeometry.Canonical.Promoted.MoorePenrose
import InfoGeometry.Canonical.Promoted.PathIntegral
import InfoGeometry.Canonical.Promoted.PerelmanW
import InfoGeometry.Canonical.Promoted.QFTTDFTLaunchpad
import InfoGeometry.Canonical.Promoted.QuantumInference
import InfoGeometry.Canonical.Promoted.RGFlow
import InfoGeometry.Canonical.Promoted.RicciMongeAmpere
import InfoGeometry.Canonical.Promoted.Rosetta
import InfoGeometry.Canonical.Promoted.SpectralInference
import InfoGeometry.Canonical.Promoted.SuperInference
import InfoGeometry.Canonical.Promoted.TomitaTakesaki
import InfoGeometry.Canonical.Promoted.TopologicalEuler
import InfoGeometry.Canonical.Promoted.TopologicalInvariants
import InfoGeometry.Canonical.Promoted.Triality
import InfoGeometry.Canonical.Promoted.WeylInformationGauge

/-!
# InfoGeometry.Canonical.ResearchPromoted

Canonical umbrella for promoted research modules.

This compatibility umbrella now re-exports the relocated
`InfoGeometry.Canonical.Promoted.*` modules while retaining the explicit
`InfoGeometry.Research.*` allowlist metadata for reviewability.
-/

/--
Strict allowlist of research modules promoted to canonical umbrellas.
This list remains explicit for reviewability.
-/
def promotedResearchAllowlist : List String :=
  [ "InfoGeometry.Research.AnalyticalIndex"
  , "InfoGeometry.Research.AQFTOperatorInterface"
  , "InfoGeometry.Research.AnomalyInflow"
  , "InfoGeometry.Research.Attention"
  , "InfoGeometry.Research.AttentionEuclidean"
  , "InfoGeometry.Research.AttentionSplit"
  , "InfoGeometry.Research.BeliefAlgebra"
  , "InfoGeometry.Research.BeliefDynamics"
  , "InfoGeometry.Research.BerryPhase"
  , "InfoGeometry.Research.BogoliubovFockSuper"
  , "InfoGeometry.Research.BottDirac"
  , "InfoGeometry.Research.BottPeriodicity"
  , "InfoGeometry.Research.BregmanTriality"
  , "InfoGeometry.Research.CalabiYauBridge"
  , "InfoGeometry.Research.CartanDecomposition"
  , "InfoGeometry.Research.CayleyBregmanBridge"
  , "InfoGeometry.Research.ChiralAction"
  , "InfoGeometry.Research.ChiralAnomaly"
  , "InfoGeometry.Research.ChiralCliffordBridge"
  , "InfoGeometry.Research.ChiralEinsteinBridge"
  , "InfoGeometry.Research.ChiralGravity"
  , "InfoGeometry.Research.ChiralRGFlow"
  , "InfoGeometry.Research.ChiralTorsionBridge"
  , "InfoGeometry.Research.CliffordBridge"
  , "InfoGeometry.Research.ConformalAlgebra"
  , "InfoGeometry.Research.ConformalUnification"
  , "InfoGeometry.Research.ConformalWard"
  , "InfoGeometry.Research.CountSubstrateBridge"
  , "InfoGeometry.Research.CurvatureRGFlow"
  , "InfoGeometry.Research.Drazin"
  , "InfoGeometry.Research.DualConnections"
  , "InfoGeometry.Research.FormalScaffold"
  , "InfoGeometry.Research.GaugeUnified"
  , "InfoGeometry.Research.GrandCanonicalExperts"
  , "InfoGeometry.Research.GrandSynthesis"
  , "InfoGeometry.Research.GrandUnification"
  , "InfoGeometry.Research.GrandUnificationBlueprint"
  , "InfoGeometry.Research.GrandUnificationMetric"
  , "InfoGeometry.Research.HeatKernel"
  , "InfoGeometry.Research.HolographicEmergence"
  , "InfoGeometry.Research.IB"
  , "InfoGeometry.Research.InformationNumber"
  , "InfoGeometry.Research.InformationTorsion"
  , "InfoGeometry.Research.KMSSinkhornBridge"
  , "InfoGeometry.Research.KaehlerGeometry"
  , "InfoGeometry.Research.KreinLadder"
  , "InfoGeometry.Research.LLN"
  , "InfoGeometry.Research.LorentzianRouting"
  , "InfoGeometry.Research.ManifoldHomology"
  , "InfoGeometry.Research.MixtureOfExperts"
  , "InfoGeometry.Research.MoorePenrose"
  , "InfoGeometry.Research.PathIntegral"
  , "InfoGeometry.Research.PerelmanW"
  , "InfoGeometry.Research.QFTTDFTLaunchpad"
  , "InfoGeometry.Research.QuantumInference"
  , "InfoGeometry.Research.RGFlow"
  , "InfoGeometry.Research.RicciMongeAmpere"
  , "InfoGeometry.Research.Rosetta"
  , "InfoGeometry.Research.SpectralInference"
  , "InfoGeometry.Research.SuperInference"
  , "InfoGeometry.Research.TomitaTakesaki"
  , "InfoGeometry.Research.TopologicalEuler"
  , "InfoGeometry.Research.TopologicalInvariants"
  , "InfoGeometry.Research.Triality"
  , "InfoGeometry.Research.WeylInformationGauge"
  ]

theorem promotedResearchAllowlist_nodup :
    promotedResearchAllowlist.Nodup := by
  native_decide
