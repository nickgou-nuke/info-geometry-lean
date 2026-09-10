import InfoGeometry.Krein.Metric
open InfoGeometry.Krein
open KreinSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
def krein_isometry_comp_self (U : NeutralSpace E →L[ℝ] NeutralSpace E) (h : IsKreinIsometry U) : IsKreinIsometry (U.comp U) :=
  IsKreinIsometry.comp h h
