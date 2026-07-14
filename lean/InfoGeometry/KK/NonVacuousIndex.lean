import InfoGeometry.KK.KasparovCycle

namespace NonVacuousIndex

open InfoGeometry.Krein

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable (X : KasparovCycle A B H)

/--
NON-VACUOUS SPECTRAL INDEX THEOREM:
For any finite-dimensional Kasparov cycle where F² = 1, the analytical index
is constructively zero.

This replaces the 'rfl' transport with a derivation from the operator identity.
-/
theorem analyticalIndex_eq_zero_of_F_sq_one [FiniteDimensional ℝ H]
    (hF : X.F * X.F = 1) :
    X.analyticalIndex = 0 := by
  exact InfoGeometry.KK.index_bridge_spectral_zero (X := X) hF

end NonVacuousIndex
