import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import InfoGeometry.Canonical.EvenCurvatureExteriorLeibnizBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
import InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.GradedChernWeilBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.EvenCurvatureExteriorLeibnizBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge

open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Theorem**: Matrix Exterior Derivative Product Rule for Homogeneous Even 2-Forms Derived Structurally from Graded Leibniz Rule. -/
theorem matrixExteriorDerivative_two_form_square
    (D : ExteriorDifferentialData R V)
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) :
    matrixExteriorDerivative D.d (F * F) =
      matrixExteriorDerivative D.d F * F + F * matrixExteriorDerivative D.d F := by
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply, Matrix.add_apply]
  rw [map_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext k
  exact two_form_leibniz D (F i k) (F k j) (hF i k)

/-- **Theorem**: Structural Covariant Derivative Product Rule for Homogeneous Even 2-Forms Derived Structurally from Graded Leibniz Rule. -/
theorem graded_covariant_two_form_square_leibniz
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F) :
    covariantDerivative A D.d (F * F) =
      covariantDerivative A D.d F * F + F * covariantDerivative A D.d F := by
  have h_d_leibniz := matrixExteriorDerivative_two_form_square D F hF
  exact covariantDerivative_square_leibniz_from_exterior_leibniz A F D.d h_d_leibniz

/-- **Theorem**: Structural Chern-Weil Closedness d(Tr(F^2)) = 0 Derived Structurally from $|F|=2$ and Graded Leibniz Rule. -/
theorem graded_bianchi_traced_chern_weil_closed
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F)
    (hBianchi : covariantDerivative A D.d F = 0) :
    D.d (matrixTraceForm (F * F)) = 0 := by
  have h_cov_leibniz := graded_covariant_two_form_square_leibniz D A F hF
  exact bianchi_implies_traced_curvature_square_closed h_cyclic A F D.d h_cov_leibniz hBianchi

/-- **Theorem**: Master Graded Chern-Weil & Covariant Leibniz Synthesis.
    Unifies:
    1. Structural matrix exterior derivative product rule for homogeneous 2-forms derived strictly from |F|=2 and D.gradedLeibniz.
    2. Structural covariant derivative product rule D_A(F^2) = (D_AF)F + F(D_AF).
    3. Structural Chern-Weil closedness d(Tr(F^2)) = 0 from Bianchi D_AF = 0 and graded differential algebra. -/
theorem master_graded_chern_weil_synthesis
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (D : ExteriorDifferentialData R V)
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hF : MatrixIsHomogeneous 2 F)
    (hBianchi : covariantDerivative A D.d F = 0) :
    (matrixExteriorDerivative D.d (F * F) =
      matrixExteriorDerivative D.d F * F + F * matrixExteriorDerivative D.d F) ∧
    (covariantDerivative A D.d (F * F) =
      covariantDerivative A D.d F * F + F * covariantDerivative A D.d F) ∧
    (D.d (matrixTraceForm (F * F)) = 0) := ⟨
  matrixExteriorDerivative_two_form_square D F hF,
  graded_covariant_two_form_square_leibniz D A F hF,
  graded_bianchi_traced_chern_weil_closed h_cyclic D A F hF hBianchi
⟩

end InfoGeometry.Canonical.GradedChernWeilBridge
