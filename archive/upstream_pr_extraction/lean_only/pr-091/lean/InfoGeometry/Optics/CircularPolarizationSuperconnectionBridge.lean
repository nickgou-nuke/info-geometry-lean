import InfoGeometry.Optics.ChiralLorentzOperatorLift
import InfoGeometry.Optics.JonesPoincareSphere
import InfoGeometry.Optics.OperatorValuedSuperconnection

noncomputable section

/-!
# Circular-polarization realization of the chiral superconnection channels

This adapter reuses the existing finite Jones projectors and the existing
nilpotent chiral matrices.  It does not introduce a second polarization
carrier or redefine the superconnection curvature.
-/

namespace InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge

open InfoGeometry.Optics.ChiralLorentzOperatorLift
open InfoGeometry.Optics.JonesPoincareSphere

abbrev CircularMatrix := Matrix (Fin 2) (Fin 2) ℂ

abbrev sigmaPlus : CircularMatrix := create
abbrev sigmaMinus : CircularMatrix := annihilate

abbrev circularPlus : CircularMatrix :=
  InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector
abbrev circularMinus : CircularMatrix :=
  InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector

def circularCommutator (A B : CircularMatrix) : CircularMatrix :=
  A * B - B * A

@[simp] theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = 0 :=
  create_sq

@[simp] theorem sigmaMinus_sq : sigmaMinus * sigmaMinus = 0 :=
  annihilate_sq

theorem sigmaPlus_mul_sigmaMinus :
    sigmaPlus * sigmaMinus = circularPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, circularPlus, create, annihilate,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector,
      FiniteJonesModel.sProjector,
      FiniteJonesModel.diagJones, Matrix.mul_apply]

theorem sigmaMinus_mul_sigmaPlus :
    sigmaMinus * sigmaPlus = circularMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, circularMinus, create, annihilate,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector,
      FiniteJonesModel.pProjector,
      FiniteJonesModel.diagJones, Matrix.mul_apply]

theorem sigmaPlus_oddOdd_eq_identity :
    sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = 1 := by
  rw [sigmaPlus_mul_sigmaMinus, sigmaMinus_mul_sigmaPlus]
  exact InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_sum_one

theorem sigmaPlus_ordinary_commutator_eq_helicity :
    circularCommutator sigmaPlus sigmaMinus = circularPlus - circularMinus := by
  simp [circularCommutator, sigmaPlus_mul_sigmaMinus,
    sigmaMinus_mul_sigmaPlus]

def circularHelicity : CircularMatrix := circularPlus - circularMinus

theorem circularHelicity_eq_commutator :
    circularHelicity = circularCommutator sigmaPlus sigmaMinus := by
  symm
  exact sigmaPlus_ordinary_commutator_eq_helicity

theorem circularHelicity_sq : circularHelicity * circularHelicity = 1 := by
  unfold circularHelicity
  calc
    (circularPlus - circularMinus) * (circularPlus - circularMinus) =
        circularPlus * circularPlus - circularPlus * circularMinus -
          (circularMinus * circularPlus - circularMinus * circularMinus) := by
            rw [sub_mul, mul_sub, mul_sub]
    _ = circularPlus - 0 - (0 - circularMinus) := by
          rw [InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector_idem,
            InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_orthogonal_left,
            InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_orthogonal_right,
            InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector_idem]
    _ = circularPlus + circularMinus := by abel
    _ = 1 := InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_sum_one

end InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge
