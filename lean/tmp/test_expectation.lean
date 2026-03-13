import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Krein.Thermal
open InfoGeometry.Krein

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "H₂" => DoubledSpace F
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable abbrev expectationFunctional (v : H₂) : EndH →L[ℝ] ℝ :=
  InfoGeometry.Canonical.KMSSinkhornBridge.expectationSeedFunctional (F := F) v

lemma kms_expectation_vacuum
    (K : EndH) (β : ℝ)
    (Ω : ThermalVacuum K)
    (hKMS : satisfies_kms_like K (expectationFunctional Ω.Omega) β) :
    satisfies_kms_like K (expectationFunctional Ω.Omega) β := hKMS
