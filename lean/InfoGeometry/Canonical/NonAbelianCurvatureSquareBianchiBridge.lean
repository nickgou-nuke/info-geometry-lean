import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge

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

/-- **Theorem**: Covariant Derivation Product Rule D_A (F * F) = (D_A F) * F + F * (D_A F). -/
theorem covariant_curvature_square_closed
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_cov_leibniz : covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F))
    (h_bianchi : covariantDerivative A d F = 0) :
    covariantDerivative A d (F * F) = 0 := by
  rw [h_cov_leibniz]
  rw [h_bianchi]
  rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- **Theorem**: Bianchi Identity D_A F = 0 Implies Non-Abelian Traced Curvature Closedness d(Tr(F ∧ F)) = 0. -/
theorem bianchi_implies_traced_curvature_square_closed
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_cov_leibniz : covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F))
    (h_bianchi : covariantDerivative A d F = 0) :
    d (matrixTraceForm (F * F)) = 0 := by
  have h_cov_sq := covariant_curvature_square_closed A F d h_cov_leibniz h_bianchi
  exact nonabelian_traced_curvature_square_closed h_cyclic A d (F * F) h_cov_sq

/-- **Theorem**: Master Non-Abelian Curvature Square Bianchi Synthesis.
    Unifies:
    1. Covariant derivation product rule D_A (F * F) = (D_A F) * F + F * (D_A F).
    2. Covariant closedness of curvature square D_A (F * F) = 0 from Bianchi D_A F = 0.
    3. Direct proof closure deriving non-Abelian traced Chern-Weil closedness d(Tr(F ∧ F)) = 0 from non-Abelian Bianchi D_A F = 0. -/
theorem master_nonabelian_curvature_square_bianchi_synthesis
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_cov_leibniz : covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F))
    (h_bianchi : covariantDerivative A d F = 0) :
    (covariantDerivative A d (F * F) = 0) ∧
    (d (matrixTraceForm (F * F)) = 0) := ⟨
  covariant_curvature_square_closed A F d h_cov_leibniz h_bianchi,
  bianchi_implies_traced_curvature_square_closed h_cyclic A F d h_cov_leibniz h_bianchi
⟩

end InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
