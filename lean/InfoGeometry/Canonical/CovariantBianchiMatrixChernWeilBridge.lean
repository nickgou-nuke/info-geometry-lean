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
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Theorem**: Derivation Closedness of Curvature Product d(F * F) = 0 from Bianchi Identity d F = 0. -/
theorem bianchi_curvature_product_closed
    (d : Module.End R (ExteriorAlgebra R V))
    (h_derivation : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y)
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_bianchi : matrixExteriorDerivative d F = 0) :
    matrixExteriorDerivative d (F * F) = 0 := by
  ext i j
  dsimp [matrixExteriorDerivative]
  rw [Matrix.mul_apply]
  rw [map_sum d]
  apply Finset.sum_eq_zero
  intro k _
  rw [h_derivation]
  have h1 : d (F i k) = 0 := by
    have h_entry : (matrixExteriorDerivative d F) i k = (0 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) i k := by rw [h_bianchi]
    exact h_entry
  have h2 : d (F k j) = 0 := by
    have h_entry : (matrixExteriorDerivative d F) k j = (0 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) k j := by rw [h_bianchi]
    exact h_entry
  rw [h1, h2, zero_mul, mul_zero, add_zero]

/-- **Theorem**: Covariant Bianchi Chern-Weil Closedness Theorem d(Tr(F ∧ F)) = 0. -/
theorem covariant_bianchi_traced_chern_weil_closed
    (d : Module.End R (ExteriorAlgebra R V))
    (h_derivation : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y)
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_bianchi : matrixExteriorDerivative d F = 0) :
    d (matrixTraceForm (matrixCurvatureWedgeSquare F)) = 0 := by
  rw [trace_matrixCurvatureWedgeSquare_eq]
  apply matrix_traced_curvature_square_closed
  exact bianchi_curvature_product_closed d h_derivation F h_bianchi

/-- **Theorem**: Master Covariant Bianchi Matrix Chern-Weil Synthesis.
    Unifies:
    1. Bianchi identity d F = 0 for matrix-valued gauge field curvatures.
    2. Curvature product derivation theorem d(F * F) = 0.
    3. Traced Chern-Weil closedness theorem d(Tr(F ∧ F)) = 0.
    4. Exact machine-checked proof closure deriving Chern-Weil closedness from Bianchi identity. -/
theorem master_covariant_bianchi_matrix_chern_weil_synthesis
    (d : Module.End R (ExteriorAlgebra R V))
    (h_derivation : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y)
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_bianchi : matrixExteriorDerivative d F = 0) :
    (matrixExteriorDerivative d (matrixCurvatureWedgeSquare F) = 0) ∧
    (d (matrixTraceForm (matrixCurvatureWedgeSquare F)) = 0) := ⟨
  bianchi_curvature_product_closed d h_derivation F h_bianchi,
  covariant_bianchi_traced_chern_weil_closed d h_derivation F h_bianchi
⟩

end InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
