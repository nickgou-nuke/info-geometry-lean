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

import InfoGeometry.Research.AnalyticalIndex
import InfoGeometry.Research.AnomalyInflow
import InfoGeometry.Research.Attention
import InfoGeometry.Research.AttentionEuclidean
import InfoGeometry.Research.AttentionSplit
import InfoGeometry.Research.BeliefAlgebra
import InfoGeometry.Research.BeliefDynamics
import InfoGeometry.Research.BerryPhase
import InfoGeometry.Research.BogoliubovFockSuper
import InfoGeometry.Research.BottDirac
import InfoGeometry.Research.BottPeriodicity
import InfoGeometry.Research.BregmanTriality
import InfoGeometry.Research.CalabiYauBridge
import InfoGeometry.Research.CartanDecomposition
import InfoGeometry.Research.CayleyBregmanBridge
import InfoGeometry.Research.ChiralAction
import InfoGeometry.Research.ChiralAnomaly
import InfoGeometry.Research.ChiralCliffordBridge
import InfoGeometry.Research.ChiralEinsteinBridge
import InfoGeometry.Research.ChiralGravity
import InfoGeometry.Research.ChiralRGFlow
import InfoGeometry.Research.ChiralTorsionBridge
import InfoGeometry.Research.CliffordBridge
import InfoGeometry.Research.ConformalAlgebra
import InfoGeometry.Research.ConformalUnification
import InfoGeometry.Research.ConformalWard
import InfoGeometry.Research.CurvatureRGFlow
import InfoGeometry.Research.Drazin
import InfoGeometry.Research.DualConnections
import InfoGeometry.Research.FormalScaffold
import InfoGeometry.Research.GaugeUnified
import InfoGeometry.Research.GrandCanonicalExperts
import InfoGeometry.Research.GrandSynthesis
import InfoGeometry.Research.GrandUnification
import InfoGeometry.Research.GrandUnificationBlueprint
import InfoGeometry.Research.GrandUnificationMetric
import InfoGeometry.Research.HeatKernel
import InfoGeometry.Research.IB
import InfoGeometry.Research.InformationNumber
import InfoGeometry.Research.InformationTorsion
import InfoGeometry.Research.KMSSinkhornBridge
import InfoGeometry.Research.KaehlerGeometry
import InfoGeometry.Research.KreinLadder
import InfoGeometry.Research.LLN
import InfoGeometry.Research.LorentzianRouting
import InfoGeometry.Research.ManifoldHomology
import InfoGeometry.Research.MixtureOfExperts
import InfoGeometry.Research.MoorePenrose
import InfoGeometry.Research.PathIntegral
import InfoGeometry.Research.PerelmanW
import InfoGeometry.Research.QuantumInference
import InfoGeometry.Research.RGFlow
import InfoGeometry.Research.RicciMongeAmpere
import InfoGeometry.Research.Rosetta
import InfoGeometry.Research.SpectralInference
import InfoGeometry.Research.SuperInference
import InfoGeometry.Research.TomitaTakesaki
import InfoGeometry.Research.TopologicalEuler
import InfoGeometry.Research.TopologicalInvariants
import InfoGeometry.Research.Triality

/-!
# InfoGeometry.Canonical.ResearchPromoted

Canonical umbrella for promoted research modules.

This file now tracks the full explicit `Research/*` allowlist (except
`InfoGeometry.Research.All`, which is itself an umbrella).
-/

/--
Strict allowlist of research modules promoted to canonical umbrellas.
This list remains explicit for reviewability.
-/
def promotedResearchAllowlist : List String :=
  [ "InfoGeometry.Research.AnalyticalIndex"
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
  ]

theorem promotedResearchAllowlist_nodup :
    promotedResearchAllowlist.Nodup := by
  native_decide
