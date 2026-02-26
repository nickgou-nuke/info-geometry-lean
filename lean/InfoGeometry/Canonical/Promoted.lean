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
import InfoGeometry.Canonical.CliffordBridge
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.ConformalWard
import InfoGeometry.Canonical.CountSubstrateBridge
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DualConnections
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.GaugeUnified
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
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.KreinLadder
import InfoGeometry.Canonical.LLN
import InfoGeometry.Canonical.LorentzianRouting
import InfoGeometry.Canonical.ManifoldHomology
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.PerelmanW
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.QuantumInference
import InfoGeometry.Canonical.RGFlow
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.Rosetta
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.SuperInference
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TopologicalEuler
import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.WeylInformationGauge

/-!
# InfoGeometry.Canonical.Promoted

Canonical umbrella for promoted canonical modules.

This compatibility umbrella now re-exports the relocated
`InfoGeometry.Canonical.*` modules while retaining the explicit
`InfoGeometry.Canonical.*` allowlist metadata for reviewability.
-/

/--
Strict allowlist of canonical promoted modules.
This list remains explicit for reviewability.
-/
def promotedCanonicalAllowlist : List String :=
  [ "InfoGeometry.Canonical.AnalyticalIndex"
  , "InfoGeometry.Canonical.AQFTOperatorInterface"
  , "InfoGeometry.Canonical.AnomalyInflow"
  , "InfoGeometry.Canonical.Attention"
  , "InfoGeometry.Canonical.AttentionEuclidean"
  , "InfoGeometry.Canonical.AttentionSplit"
  , "InfoGeometry.Canonical.BeliefAlgebra"
  , "InfoGeometry.Canonical.BeliefDynamics"
  , "InfoGeometry.Canonical.BerryPhase"
  , "InfoGeometry.Canonical.BogoliubovFockSuper"
  , "InfoGeometry.Canonical.BottDirac"
  , "InfoGeometry.Canonical.BottPeriodicity"
  , "InfoGeometry.Canonical.BregmanTriality"
  , "InfoGeometry.Canonical.CalabiYauBridge"
  , "InfoGeometry.Canonical.CartanDecomposition"
  , "InfoGeometry.Canonical.CayleyBregmanBridge"
  , "InfoGeometry.Canonical.ChiralAction"
  , "InfoGeometry.Canonical.ChiralAnomaly"
  , "InfoGeometry.Canonical.ChiralCliffordBridge"
  , "InfoGeometry.Canonical.ChiralEinsteinBridge"
  , "InfoGeometry.Canonical.ChiralGravity"
  , "InfoGeometry.Canonical.ChiralRGFlow"
  , "InfoGeometry.Canonical.ChiralTorsionBridge"
  , "InfoGeometry.Canonical.CliffordBridge"
  , "InfoGeometry.Canonical.ConformalAlgebra"
  , "InfoGeometry.Canonical.ConformalUnification"
  , "InfoGeometry.Canonical.ConformalWard"
  , "InfoGeometry.Canonical.CountSubstrateBridge"
  , "InfoGeometry.Canonical.CurvatureRGFlow"
  , "InfoGeometry.Canonical.Drazin"
  , "InfoGeometry.Canonical.DualConnections"
  , "InfoGeometry.Canonical.FormalScaffold"
  , "InfoGeometry.Canonical.GaugeUnified"
  , "InfoGeometry.Canonical.GrandCanonicalExperts"
  , "InfoGeometry.Canonical.GrandSynthesis"
  , "InfoGeometry.Canonical.GrandUnification"
  , "InfoGeometry.Canonical.GrandUnificationBlueprint"
  , "InfoGeometry.Canonical.GrandUnificationMetric"
  , "InfoGeometry.Canonical.HeatKernel"
  , "InfoGeometry.Canonical.HolographicEmergence"
  , "InfoGeometry.Canonical.IB"
  , "InfoGeometry.Canonical.InformationNumber"
  , "InfoGeometry.Canonical.InformationTorsion"
  , "InfoGeometry.Canonical.KMSSinkhornBridge"
  , "InfoGeometry.Canonical.KaehlerGeometry"
  , "InfoGeometry.Canonical.KreinLadder"
  , "InfoGeometry.Canonical.LLN"
  , "InfoGeometry.Canonical.LorentzianRouting"
  , "InfoGeometry.Canonical.ManifoldHomology"
  , "InfoGeometry.Canonical.MixtureOfExperts"
  , "InfoGeometry.Canonical.MoorePenrose"
  , "InfoGeometry.Canonical.PathIntegral"
  , "InfoGeometry.Canonical.PerelmanW"
  , "InfoGeometry.Canonical.QFTTDFTLaunchpad"
  , "InfoGeometry.Canonical.QuantumInference"
  , "InfoGeometry.Canonical.RGFlow"
  , "InfoGeometry.Canonical.RicciMongeAmpere"
  , "InfoGeometry.Canonical.Rosetta"
  , "InfoGeometry.Canonical.SpectralInference"
  , "InfoGeometry.Canonical.SuperInference"
  , "InfoGeometry.Canonical.TomitaTakesaki"
  , "InfoGeometry.Canonical.TopologicalEuler"
  , "InfoGeometry.Canonical.TopologicalInvariants"
  , "InfoGeometry.Canonical.Triality"
  , "InfoGeometry.Canonical.WeylInformationGauge"
  ]

theorem promotedCanonicalAllowlist_nodup :
    promotedCanonicalAllowlist.Nodup := by
  native_decide
