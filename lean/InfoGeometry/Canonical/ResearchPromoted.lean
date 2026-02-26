import InfoGeometry.Research.AnalyticalIndex
import InfoGeometry.Research.BregmanTriality
import InfoGeometry.Research.BottDirac
import InfoGeometry.Research.BottPeriodicity
import InfoGeometry.Research.CalabiYauBridge
import InfoGeometry.Research.CartanDecomposition
import InfoGeometry.Research.CayleyBregmanBridge
import InfoGeometry.Research.ChiralAction
import InfoGeometry.Research.ChiralAnomaly
import InfoGeometry.Research.ChiralCliffordBridge
import InfoGeometry.Research.CliffordBridge
import InfoGeometry.Research.ConformalAlgebra
import InfoGeometry.Research.ConformalUnification
import InfoGeometry.Research.CurvatureRGFlow
import InfoGeometry.Research.Drazin
import InfoGeometry.Research.DualConnections
import InfoGeometry.Research.InformationNumber
import InfoGeometry.Research.InformationTorsion
import InfoGeometry.Research.KMSSinkhornBridge
import InfoGeometry.Research.MoorePenrose
import InfoGeometry.Research.PerelmanW
import InfoGeometry.Research.RGFlow
import InfoGeometry.Research.SpectralInference
import InfoGeometry.Research.TopologicalEuler
import InfoGeometry.Research.Triality
import InfoGeometry.Research.GrandSynthesis

/-!
# InfoGeometry.Canonical.ResearchPromoted

Curated Tier-1 research modules promoted into the canonical/library umbrellas.

Selection criteria for this promotion patch:
- module builds cleanly under `--wfail`
- no unfinished proof-gap markers
- no literal-zero placeholder core defs in the promoted file itself
- small API surfaces with compatibility aliases where needed
-/

/--
Strict allowlist of research modules promoted to canonical umbrellas.
This list is intentionally explicit so promotion remains reviewable PR-by-PR.
-/
def promotedResearchAllowlist : List String :=
  [ "InfoGeometry.Research.AnalyticalIndex"
  , "InfoGeometry.Research.BregmanTriality"
  , "InfoGeometry.Research.BottDirac"
  , "InfoGeometry.Research.BottPeriodicity"
  , "InfoGeometry.Research.CalabiYauBridge"
  , "InfoGeometry.Research.CartanDecomposition"
  , "InfoGeometry.Research.CayleyBregmanBridge"
  , "InfoGeometry.Research.ChiralAction"
  , "InfoGeometry.Research.ChiralAnomaly"
  , "InfoGeometry.Research.ChiralCliffordBridge"
  , "InfoGeometry.Research.CliffordBridge"
  , "InfoGeometry.Research.ConformalAlgebra"
  , "InfoGeometry.Research.ConformalUnification"
  , "InfoGeometry.Research.CurvatureRGFlow"
  , "InfoGeometry.Research.Drazin"
  , "InfoGeometry.Research.DualConnections"
  , "InfoGeometry.Research.GrandSynthesis"
  , "InfoGeometry.Research.InformationNumber"
  , "InfoGeometry.Research.InformationTorsion"
  , "InfoGeometry.Research.KMSSinkhornBridge"
  , "InfoGeometry.Research.MoorePenrose"
  , "InfoGeometry.Research.PerelmanW"
  , "InfoGeometry.Research.RGFlow"
  , "InfoGeometry.Research.SpectralInference"
  , "InfoGeometry.Research.TopologicalEuler"
  , "InfoGeometry.Research.Triality"
  ]

theorem promotedResearchAllowlist_nodup :
    promotedResearchAllowlist.Nodup := by
  native_decide
