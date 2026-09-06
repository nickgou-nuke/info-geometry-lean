/-
InfoGeometry/Geometry/ConstructiveConnesChern.lean
-/

import InfoGeometry.Geometry.ConstructiveKasparov
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Geometry.SpectralDivisors

noncomputable section

namespace InfoGeometry.Geometry.ConstructiveConnesChern

open InfoGeometry.Geometry.ConstructiveKasparov
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.SpectralDivisors

abbrev ConnesChernDatum
    {Region Point Tangent A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Ring A]
    (_I : GeometricIntegralBackend Region Point Tangent A)
    (_D : VerifiedBoundedDirac A) :=
  OperatorOneForm Point Tangent A

namespace ConnesChernDatum

abbrev ccForm
    {Region Point Tangent A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Ring A]
    {I : GeometricIntegralBackend Region Point Tangent A}
    {D : VerifiedBoundedDirac A}
    (CC : ConnesChernDatum I D) : OperatorOneForm Point Tangent A := CC

end ConnesChernDatum

theorem index_eq_boundary_integral
    {Region Point Tangent A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Ring A]
    (I : GeometricIntegralBackend Region Point Tangent A)
    (D : VerifiedBoundedDirac A)
    (CC : ConnesChernDatum I D)
    (hCC : ∀ p : Point, I.geometricDerivative CC.ccForm p = D.P)
    (Ω : Region) :
    I.boundaryIntegral Ω CC.ccForm =
      I.volumeIntegral Ω (fun _ => D.P) := by
  have stokes := I.stokes_eq Ω CC.ccForm
  have defect_subst :
      I.geometricDerivative CC.ccForm = fun _ => D.P := by
    ext p
    exact hCC p
  rw [defect_subst] at stokes
  exact stokes

theorem kasparov_defect_is_quantized
    {Region Point Tangent A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [Ring A]
    (I : GeometricIntegralBackend Region Point Tangent A)
    (D : VerifiedBoundedDirac A)
    (CC : ConnesChernDatum I D)
    (hCC : ∀ p : Point, I.geometricDerivative CC.ccForm p = D.P)
    (N : PhaseResidueNormalizer A)
    (W : WindingNumberDatum I N CC.ccForm)
    (Ω : Region) :
    I.volumeIntegral Ω (fun _ => D.P) =
      (W.winding Ω : ℝ) • N.phasePeriod := by
  have h_index := (index_eq_boundary_integral I D CC hCC Ω).symm
  have h_wind := W.boundaryIntegral_eq_winding_smul Ω
  rw [h_index]
  exact h_wind

end InfoGeometry.Geometry.ConstructiveConnesChern
