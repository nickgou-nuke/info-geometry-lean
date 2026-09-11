import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Physics.LorentzBoostMinkowski
import InfoGeometry.Optics.JonesPoincareSphere

/-!
# Finite Dirac and Stokes four-vector readouts

This owner records only finite matrix identities.  It does not construct a
Poincare representation or a Pauli--Lubanski operator.  The Dirac identity is
the concrete Clifford linearisation of the Minkowski quadratic form, while
the Stokes statement reuses the existing Jones/Pauli null readout.
-/

noncomputable section

namespace InfoGeometry.Physics.FourVectorDiracReadout

open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Optics.JonesPoincareSphere

/-- The finite Dirac slash of a real `(+---)` four-vector. -/
def diracSlash (p : FourVector) : DiracMatrix :=
  (p.t : ℂ) • gamma 0 + (p.x : ℂ) • gamma 1 +
    (p.y : ℂ) • gamma 2 + (p.z : ℂ) • gamma 3

theorem diracSlash_sq (p : FourVector) :
    diracSlash p * diracSlash p =
      (minkowskiSq p : ℂ) • (1 : DiracMatrix) := by
  rcases p with ⟨t, x, y, z⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3,
      minkowskiSq, minkowskiPair, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply] <;>
    ring_nf <;>
    simp <;>
    ring

theorem diracSlash_square_readout (p : FourVector) :
    diracSlash p * diracSlash p =
      (minkowskiSq p : ℂ) • (1 : DiracMatrix) :=
  diracSlash_sq p

/-- The finite Stokes carrier is null in the Pauli/Hestenes quadratic form. -/
theorem stokes_pauli_determinant_zero (J : JonesSpinor) :
    Matrix.det (InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix
      (JonesSpinor.stokesMinkowski4 J)) = 0 := by
  exact JonesSpinor.stokesPauli_det_zero J

end InfoGeometry.Physics.FourVectorDiracReadout
