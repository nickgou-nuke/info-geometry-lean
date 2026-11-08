import InfoGeometry.Krein.PolarizedSector

open scoped InnerProductSpace

namespace InfoGeometry.Krein.DoubleRealKreinProjectorPairing

open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H2" => DoubledSpace E
local notation "Pplus" => spectralPlusProj (E := E)
local notation "Pminus" => spectralMinusProj (E := E)

/-- The indefinite pairing on the real doubled Krein carrier is the positive
    Hilbert pairing of its positive spectral component minus that of its
    negative spectral component. -/
theorem kreinInner_eq_spectral_projector_difference (u v : H2) :
    KreinSpace.kreinInner (H := H2) u v =
      inner ℝ (Pplus u) (Pplus v) - inner ℝ (Pminus u) (Pminus v) := by
  rw [krein_inner_prod_l2]
  rw [spectralPlusProj_apply_eq_plusPoint, spectralPlusProj_apply_eq_plusPoint,
    spectralMinusProj_apply_eq_minusPoint, spectralMinusProj_apply_eq_minusPoint]
  simp [plusPoint, minusPoint, to_doubled, WithLp.prod_inner_apply]

end InfoGeometry.Krein.DoubleRealKreinProjectorPairing
