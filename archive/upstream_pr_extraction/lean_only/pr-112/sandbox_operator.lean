import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

noncomputable def circularCoordinateLinearEquiv : CZ ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  circularPeirceBasis.equivFun

noncomputable def circularOperatorReadout : Module.End ℝ CZ ≃ₐ[ℝ] Module.End ℝ (Fin 8 → ℝ) :=
  circularCoordinateLinearEquiv.conjAlgEquiv ℝ

#check LinearMap.mulLeft ℝ zornPlus
#check LinearMap.mulRight ℝ zornMinus
