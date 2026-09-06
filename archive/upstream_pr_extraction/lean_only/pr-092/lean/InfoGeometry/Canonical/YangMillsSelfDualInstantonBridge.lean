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
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Definition**: Matrix Hodge Star Operator on Matrix-Valued Exterior Forms. -/
def matrixHodgeStar
    (star : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  Matrix.of (fun i j => star (M i j))

/-- **Definition**: Self-Dual Yang-Mills Curvature Condition ★ F = F. -/
def isSelfDualCurvature
    (star : Module.End R (ExteriorAlgebra R V))
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) : Prop :=
  matrixHodgeStar star F = F

/-- **Definition**: Anti-Self-Dual Yang-Mills Curvature Condition ★ F = -F. -/
def isAntiSelfDualCurvature
    (star : Module.End R (ExteriorAlgebra R V))
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) : Prop :=
  matrixHodgeStar star F = -F

/-- **Theorem**: Self-Dual Instantons Solve Vacuum Yang-Mills Equations D_A (★ F_A) = 0 via Bianchi D_A F_A = 0. -/
theorem self_dual_solves_yang_mills
    (star : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_self_dual : isSelfDualCurvature star F)
    (h_bianchi : covariantDerivative A d F = 0) :
    covariantDerivative A d (matrixHodgeStar star F) = 0 := by
  rw [h_self_dual]
  exact h_bianchi

/-- **Theorem**: Anti-Self-Dual Instantons Solve Vacuum Yang-Mills Equations D_A (★ F_A) = 0 via Bianchi D_A F_A = 0. -/
theorem anti_self_dual_solves_yang_mills
    (star : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_anti_self_dual : isAntiSelfDualCurvature star F)
    (h_cov_neg : covariantDerivative A d (-F) = - covariantDerivative A d F)
    (h_bianchi : covariantDerivative A d F = 0) :
    covariantDerivative A d (matrixHodgeStar star F) = 0 := by
  rw [h_anti_self_dual]
  rw [h_cov_neg]
  rw [h_bianchi]
  exact neg_zero

end InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
