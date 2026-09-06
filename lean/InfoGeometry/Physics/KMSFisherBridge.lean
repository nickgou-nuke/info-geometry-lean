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
abbrev ComplexCrossProduct3 := InfoGeometry.Algebra.Zorn.CrossProduct3 ℂ

/-- Information potential / modular Hamiltonian attached to the split norm. -/
def modularHamiltonian (cp : ComplexCrossProduct3) (X : ComplexZornMatrix) : ℂ :=
  -Complex.log (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X)

/-- Scalar Fisher weight induced by the split determinant. -/
def fisherWeight (cp : ComplexCrossProduct3) (X : ComplexZornMatrix) : ℂ :=
  1 / (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X) ^ 2

/-- Determinant equality transports the modular Hamiltonian unchanged. -/
theorem modularHamiltonian_of_det_eq
    (cp : ComplexCrossProduct3) (X Y : ComplexZornMatrix)
    (hdet : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y) :
    modularHamiltonian cp X = modularHamiltonian cp Y := by
  simp [modularHamiltonian, hdet]

/-- Determinant equality transports the scalar Fisher weight unchanged. -/
theorem fisherWeight_of_det_eq
    (cp : ComplexCrossProduct3) (X Y : ComplexZornMatrix)
    (hdet : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y) :
    fisherWeight cp X = fisherWeight cp Y := by
  simp [fisherWeight, hdet]

/-- Re-export of the owner polarization identity for the TKK Fisher pairing. -/
theorem tkkFisher_eq_det_polar
    (cp : ComplexCrossProduct3) (X Y : ComplexZornMatrix) :
    InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric cp X Y =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp (X + Y) -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp X -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ cp Y := by
  exact InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric_eq_detZ_polar cp X Y

/-- Re-export of the owner symmetry theorem for the TKK Fisher pairing. -/
theorem tkkFisher_symm
    (cp : ComplexCrossProduct3) (X Y : ComplexZornMatrix) :
    InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric cp X Y =
      InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric cp Y X := by
  exact InfoGeometry.Physics.TKKZorn.TKKFisherInformationMetric_symm cp X Y

end

end InfoGeometry.Physics
