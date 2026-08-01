import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
import InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
import InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CurvatureFromConnectionBianchiBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Theorem**: Matrix Exterior Derivative Additivity d(M + N) = dM + dN. -/
theorem matrixExteriorDerivative_add
    (d : Module.End R (ExteriorAlgebra R V))
    (M N : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixExteriorDerivative d (M + N) = matrixExteriorDerivative d M + matrixExteriorDerivative d N := by
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.add_apply]
  exact LinearMap.map_add d (M i j) (N i j)

/-- **Theorem**: Matrix Commutator of Matrix with its Square vanishes [A, A * A] = 0. -/
theorem matrixCommutator_cube_zero (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixCommutator A (A * A) = 0 := by
  dsimp [matrixCommutator]
  rw [Matrix.mul_assoc]
  rw [sub_self]

/-- **Theorem**: Genuine Derivation of Connection Curvature Bianchi Identity D_A F_A = 0 from Nilpotency d² = 0 & Derivation Product Rule. -/
theorem curvatureFromConnection_bianchi
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (hd2_A : matrixExteriorDerivative d (matrixExteriorDerivative d A) = 0)
    (h_d_A_square :
      matrixExteriorDerivative d (A * A) =
        matrixExteriorDerivative d A * A - A * matrixExteriorDerivative d A) :
    covariantDerivative A d (curvatureFromConnection d A) = 0 := by
  dsimp [covariantDerivative, curvatureFromConnection, matrixCommutator]
  rw [matrixExteriorDerivative_add]
  rw [hd2_A]
  rw [h_d_A_square]
  rw [zero_add]
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [Matrix.mul_assoc A A A]
  abel

/-- **Theorem**: Unconditional Self-Dual Yang-Mills Field Equation Solution D_A (★ F_A) = 0 without Primitive Bianchi Assumption. -/
theorem unconditional_self_dual_yang_mills
    (star : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (hd2_A : matrixExteriorDerivative d (matrixExteriorDerivative d A) = 0)
    (h_d_A_square :
      matrixExteriorDerivative d (A * A) =
        matrixExteriorDerivative d A * A - A * matrixExteriorDerivative d A)
    (h_self_dual : isSelfDualCurvature star (curvatureFromConnection d A)) :
    covariantDerivative A d (matrixHodgeStar star (curvatureFromConnection d A)) = 0 := by
  have h_bianchi := curvatureFromConnection_bianchi A d hd2_A h_d_A_square
  exact self_dual_connection_curvature_solves_yang_mills star A d h_self_dual h_bianchi

/-- **Theorem**: Unconditional Anti-Self-Dual Yang-Mills Field Equation Solution D_A (★ F_A) = 0 without Primitive Bianchi Assumption. -/
theorem unconditional_anti_self_dual_yang_mills
    (star : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (hd2_A : matrixExteriorDerivative d (matrixExteriorDerivative d A) = 0)
    (h_d_A_square :
      matrixExteriorDerivative d (A * A) =
        matrixExteriorDerivative d A * A - A * matrixExteriorDerivative d A)
    (h_anti_self_dual : isAntiSelfDualCurvature star (curvatureFromConnection d A)) :
    covariantDerivative A d (matrixHodgeStar star (curvatureFromConnection d A)) = 0 := by
  have h_bianchi := curvatureFromConnection_bianchi A d hd2_A h_d_A_square
  exact anti_self_dual_connection_curvature_solves_yang_mills star A d h_anti_self_dual h_bianchi


end InfoGeometry.Canonical.CurvatureFromConnectionBianchiBridge
