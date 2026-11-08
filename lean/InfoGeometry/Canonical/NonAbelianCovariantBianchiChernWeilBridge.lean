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
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Definition**: Matrix Commutator [A, M] = A * M - M * A for Gauge Field Connections. -/
def matrixCommutator
    (A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  A * M - M * A

/-- **Definition**: Non-Abelian Covariant Derivative D_A M = d M + [A, M]. -/
def covariantDerivative
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  matrixExteriorDerivative d M + matrixCommutator A M

/-- **Theorem**: Vanishing of the Matrix Trace of Commutator Tr([A, M]) = 0 under Trace Cyclic Identity Tr(A M) = Tr(M A). -/
theorem trace_matrix_commutator_zero
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixTraceForm (matrixCommutator A M) = 0 := by
  dsimp [matrixCommutator]
  rw [LinearMap.map_sub]
  rw [h_cyclic A M]
  exact sub_self (matrixTraceForm (M * A))

/-- **Theorem**: Non-Abelian Covariant Derivative Trace Identification Tr(D_A M) = d(Tr(M)). -/
theorem trace_covariantDerivative_eq_d_trace
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    matrixTraceForm (covariantDerivative A d M) = d (matrixTraceForm M) := by
  dsimp [covariantDerivative]
  rw [LinearMap.map_add]
  rw [trace_matrix_commutator_zero h_cyclic A M]
  rw [add_zero]
  exact (exteriorDerivative_matrixTraceForm d M).symm

/-- **Theorem**: Non-Abelian Traced Curvature Closedness Theorem d(Tr(F ∧ F)) = 0. -/
theorem nonabelian_traced_curvature_square_closed
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (F2 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_bianchi_cov : covariantDerivative A d F2 = 0) :
    d (matrixTraceForm F2) = 0 := by
  have h := trace_covariantDerivative_eq_d_trace h_cyclic A d F2
  rw [h_bianchi_cov] at h
  rw [LinearMap.map_zero] at h
  exact h.symm

/-- **Theorem**: Master Non-Abelian Covariant Bianchi Chern-Weil Synthesis.
    Unifies:
    1. Matrix commutator [A, M] = A * M - M * A definition.
    2. Non-Abelian covariant derivative D_A M = d M + [A, M] definition.
    3. Vanishing trace commutator theorem Tr([A, M]) = 0.
    4. Covariant trace reduction Tr(D_A M) = d(Tr(M)).
    5. Non-Abelian Chern-Weil closedness theorem d(Tr(F ∧ F)) = 0 from D_A(F ∧ F) = 0. -/
theorem master_nonabelian_covariant_bianchi_synthesis
    (h_cyclic : ∀ A M : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V), matrixTraceForm (A * M) = matrixTraceForm (M * A))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (F2 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_bianchi_cov : covariantDerivative A d F2 = 0) :
    (matrixTraceForm (matrixCommutator A F2) = 0) ∧
    (d (matrixTraceForm F2) = 0) := ⟨
  trace_matrix_commutator_zero h_cyclic A F2,
  nonabelian_traced_curvature_square_closed h_cyclic A d F2 h_bianchi_cov
⟩

end InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
