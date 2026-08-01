import InfoGeometry.Physics.TKKZorn
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
KMS-Fisher bridge on the repo-native Zorn carrier.
This file only packages consequences of already existing owner theorems.
-/

open InfoGeometry.Algebra.Zorn

namespace InfoGeometry.Physics

noncomputable section

abbrev ComplexZornMatrix := InfoGeometry.Algebra.Zorn.ZornMatrix ℂ
/-- Information potential / modular Hamiltonian attached to the split norm. -/
def modularHamiltonian (X : ComplexZornMatrix) : ℂ :=
  -Complex.log (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X)

/-- Scalar Fisher weight induced by the split determinant. -/
def fisherWeight (X : ComplexZornMatrix) : ℂ :=
  1 / (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X) ^ 2

/-- Determinant equality transports the modular Hamiltonian unchanged. -/
theorem modularHamiltonian_of_det_eq
    (X Y : ComplexZornMatrix)
    (hdet : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Y) :
    modularHamiltonian X = modularHamiltonian Y := by
  simp [modularHamiltonian, hdet]

/-- Determinant equality transports the scalar Fisher weight unchanged. -/
theorem fisherWeight_of_det_eq
    (X Y : ComplexZornMatrix)
    (hdet : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Y) :
    fisherWeight X = fisherWeight Y := by
  simp [fisherWeight, hdet]

/-- Re-export of the owner polarization identity for the TKK Fisher pairing. -/
theorem tkkFisher_eq_det_polar
    (X Y : ComplexZornMatrix) :
    InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric X Y =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (X + Y) -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Y := by
  exact InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric_eq_detZ_polar X Y

/-- Re-export of the owner symmetry theorem for the TKK Fisher pairing. -/
theorem tkkFisher_symm
    (X Y : ComplexZornMatrix) :
    InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric X Y =
      InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric Y X := by
  exact InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric_symm X Y

end

end InfoGeometry.Physics
