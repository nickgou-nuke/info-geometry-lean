import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import InfoGeometry.Canonical.CurvatureFromConnectionBianchiBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.GradedConnectionBianchiBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.CurvatureFromConnectionBianchiBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge

open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Theorem**: Matrix Exterior Derivative Operator Nilpotency d^2 A = 0 Derived Structurally from D.sq_zero. -/
theorem matrixExteriorDerivative_sq_zero
    (D : ExteriorDifferentialData R V)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixExteriorDerivative D.d (matrixExteriorDerivative D.d A) = 0 := by
  ext i j
  dsimp [matrixExteriorDerivative]
  exact LinearMap.congr_fun D.sq_zero (A i j)

/-- **Theorem**: Matrix Exterior Derivative Product Rule d(A·A) = dA·A - A·dA for 1-Forms Derived Structurally from Graded Leibniz Rule and |A|=1. -/
theorem matrix_one_form_square_leibniz
    (D : ExteriorDifferentialData R V)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    matrixExteriorDerivative D.d (A * A) =
      matrixExteriorDerivative D.d A * A - A * matrixExteriorDerivative D.d A := by
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply, Matrix.sub_apply]
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext k
  exact one_form_leibniz D (A i k) (A k j) (hA i k)

/-- **Theorem**: Structural Non-Tautological Bianchi Derivation D_A F_A = 0 Derived Structurally from D.sq_zero, Graded 1-Form Leibniz Rule, and |A|=1. -/
theorem graded_connection_curvature_bianchi
    (D : ExteriorDifferentialData R V)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    covariantDerivative A D.d (curvatureFromConnection D.d A) = 0 := by
  have hd2_A := matrixExteriorDerivative_sq_zero D A
  have h_d_A_square := matrix_one_form_square_leibniz D A hA
  exact curvatureFromConnection_bianchi A D.d hd2_A h_d_A_square

/-- **Theorem**: Master Graded Connection Bianchi Synthesis.
    Unifies:
    1. Matrix exterior derivative operator nilpotency d^2 A = 0 derived strictly from D.sq_zero.
    2. Matrix exterior derivative product rule d(A·A) = dA·A - A·dA for 1-forms derived strictly from |A|=1 and D.gradedLeibniz.
    3. Structural non-tautological Bianchi identity derivation D_A F_A = 0 without primitive Bianchi, nilpotency, or Leibniz parameters. -/
theorem master_graded_connection_bianchi_synthesis
    (D : ExteriorDifferentialData R V)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    (matrixExteriorDerivative D.d (matrixExteriorDerivative D.d A) = 0) ∧
    (matrixExteriorDerivative D.d (A * A) =
      matrixExteriorDerivative D.d A * A - A * matrixExteriorDerivative D.d A) ∧
    (covariantDerivative A D.d (curvatureFromConnection D.d A) = 0) := ⟨
  matrixExteriorDerivative_sq_zero D A,
  matrix_one_form_square_leibniz D A hA,
  graded_connection_curvature_bianchi D A hA
⟩

end InfoGeometry.Canonical.GradedConnectionBianchiBridge
