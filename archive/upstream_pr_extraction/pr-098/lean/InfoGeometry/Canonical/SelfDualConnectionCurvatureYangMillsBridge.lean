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
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Lemma**: Covariant Derivative Negation Linearity D_A (-M) = - D_A M. -/
theorem covariantDerivative_neg
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    covariantDerivative A d (-M) = - covariantDerivative A d M := by
  dsimp [covariantDerivative, matrixCommutator]
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply]
  rw [LinearMap.map_neg]
  simp_rw [mul_neg, neg_mul, Finset.sum_neg_distrib]
  noncomm_ring

/-- **Theorem**: Direct Connection Curvature Self-Dual Instanton Solution D_A (★ F_A) = 0 via Bianchi D_A F_A = 0. -/
theorem self_dual_connection_curvature_solves_yang_mills
    (star : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_self_dual : isSelfDualCurvature star (curvatureFromConnection d A))
    (h_bianchi : covariantDerivative A d (curvatureFromConnection d A) = 0) :
    covariantDerivative A d (matrixHodgeStar star (curvatureFromConnection d A)) = 0 := by
  exact self_dual_solves_yang_mills star A d (curvatureFromConnection d A) h_self_dual h_bianchi

/-- **Theorem**: Direct Connection Curvature Anti-Self-Dual Instanton Solution D_A (★ F_A) = 0 via Bianchi D_A F_A = 0. -/
theorem anti_self_dual_connection_curvature_solves_yang_mills
    (star : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_anti_self_dual : isAntiSelfDualCurvature star (curvatureFromConnection d A))
    (h_bianchi : covariantDerivative A d (curvatureFromConnection d A) = 0) :
    covariantDerivative A d (matrixHodgeStar star (curvatureFromConnection d A)) = 0 := by
  have h_cov_neg := covariantDerivative_neg A d (curvatureFromConnection d A)
  exact anti_self_dual_solves_yang_mills star A d (curvatureFromConnection d A) h_anti_self_dual h_cov_neg h_bianchi


end InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
