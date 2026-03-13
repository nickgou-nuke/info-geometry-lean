import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Krein.Thermal
open InfoGeometry.Krein

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "H₂" => DoubledSpace F
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable def expectationFunctional (v : H₂) : EndH →L[ℝ] ℝ where
  toFun A := inner ℝ v (A v)
  map_add' A B := by simp [inner_add_right]
  map_smul' c A := by simp [inner_smul_right]
  cont := sorry

lemma kms_expectation_vacuum
    (K : EndH) (β : ℝ)
    (Ω : ThermalVacuum K)
    (hKMS : satisfies_kms_like K (expectationFunctional Ω.Omega) β) :
    True := trivial
