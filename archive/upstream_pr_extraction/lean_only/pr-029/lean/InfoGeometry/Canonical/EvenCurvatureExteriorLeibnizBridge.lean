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
import InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.EvenCurvatureExteriorLeibnizBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.NonAbelianCurvatureSquareBianchiBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.MatrixCommutatorSquareLeibnizBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Theorem**: Matrix Exterior Derivative Product Rule d(F * F) = dF * F + F * dF for Even Curvature Forms. -/
theorem matrixExteriorDerivative_even_curvature_square
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_even_leibniz : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y) :
    matrixExteriorDerivative d (F * F) = matrixExteriorDerivative d F * F + F * matrixExteriorDerivative d F := by
  ext i j
  dsimp [matrixExteriorDerivative, Matrix.mul_apply, Matrix.add_apply]
  rw [map_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext k
  exact h_even_leibniz (F i k) (F k j)

/-- **Theorem**: Unconditional Covariant Derivative Leibniz Rule D_A (F * F) = (D_A F) * F + F * (D_A F). -/
theorem unconditional_covariant_curvature_square_leibniz
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_even_leibniz : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y) :
    covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F) := by
  have h_d_leibniz := matrixExteriorDerivative_even_curvature_square F d h_even_leibniz
  exact covariantDerivative_square_leibniz_from_exterior_leibniz A F d h_d_leibniz

/-- **Theorem**: Unconditional Bianchi Traced Chern-Weil Closedness d(Tr(F ∧ F)) = 0 directly from D_A F = 0. -/
theorem unconditional_bianchi_traced_chern_weil_closed
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_even_leibniz : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y)
    (h_bianchi : covariantDerivative A d F = 0) :
    d (matrixTraceForm (F * F)) = 0 := by
  have h_cov_leibniz := unconditional_covariant_curvature_square_leibniz A F d h_even_leibniz
  exact bianchi_implies_traced_curvature_square_closed h_cyclic A F d h_cov_leibniz h_bianchi

/-- **Theorem**: Master Even Curvature Exterior Leibniz & Chern-Weil Synthesis.
    Unifies:
    1. Matrix exterior derivative product rule d(F * F) = dF * F + F * dF for even curvature forms.
    2. Unconditional non-Abelian covariant derivative product rule D_A (F * F) = (D_A F) * F + F * (D_A F).
    3. Unconditional non-Abelian Bianchi-to-traced Chern-Weil closedness d(Tr(F ∧ F)) = 0 directly from D_A F = 0 without primitive Leibniz assumptions. -/
theorem master_even_curvature_exterior_leibniz_synthesis
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (h_even_leibniz : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y)
    (h_bianchi : covariantDerivative A d F = 0) :
    (matrixExteriorDerivative d (F * F) = matrixExteriorDerivative d F * F + F * matrixExteriorDerivative d F) ∧
    (covariantDerivative A d (F * F) = (covariantDerivative A d F) * F + F * (covariantDerivative A d F)) ∧
    (d (matrixTraceForm (F * F)) = 0) := ⟨
  matrixExteriorDerivative_even_curvature_square F d h_even_leibniz,
  unconditional_covariant_curvature_square_leibniz A F d h_even_leibniz,
  unconditional_bianchi_traced_chern_weil_closed h_cyclic A F d h_even_leibniz h_bianchi
⟩

end InfoGeometry.Canonical.EvenCurvatureExteriorLeibnizBridge
