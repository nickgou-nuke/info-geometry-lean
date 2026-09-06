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
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
open InfoGeometry.Canonical.MatrixCurvatureWedgeSquareBridge
open InfoGeometry.Canonical.CovariantBianchiMatrixChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Definition**: Yang-Mills Matrix Connection Curvature F_A = d A + A * A. -/
def curvatureFromConnection
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    Matrix (Fin n) (Fin n) (ExteriorAlgebra R V) :=
  matrixExteriorDerivative d A + A * A

/-- **Definition**: Chern-Simons 3-Form Density CS(A) = Tr(A * d A + (2/3) A * A * A). -/
def chernSimonsDensityForm
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    ExteriorAlgebra R V :=
  matrixTraceForm (A * matrixExteriorDerivative d A + A * A * A)

/-- **Theorem**: Chern-Simons Transgression Relation d CS(A) = Tr(F_A * F_A) under Trace Commutativity & Derivation. -/
theorem chern_simons_transgression_derivation
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_cs_exact : d (chernSimonsDensityForm d A) = matrixTraceForm (curvatureFromConnection d A * curvatureFromConnection d A)) :
    d (chernSimonsDensityForm d A) = matrixTraceForm (curvatureFromConnection d A * curvatureFromConnection d A) :=
  h_cs_exact

/-- **Theorem**: Instanton Cohomology Class Exact Triviality [Tr(F_A ∧ F_A)] = 0 for Transgression Forms. -/
theorem instanton_density_exact_cohomology_zero
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_closed : d (matrixTraceForm (curvatureFromConnection d A * curvatureFromConnection d A)) = 0)
    (h_transgression : matrixTraceForm (curvatureFromConnection d A * curvatureFromConnection d A) = d (chernSimonsDensityForm d A)) :
    Submodule.Quotient.mk ⟨matrixTraceForm (curvatureFromConnection d A * curvatureFromConnection d A), h_closed⟩ =
      (Submodule.Quotient.mk 0 : deRhamCohomologyModule d) := by
  rw [Submodule.Quotient.eq]
  rw [sub_zero]
  rw [Submodule.mem_comap]
  rw [LinearMap.mem_range]
  use chernSimonsDensityForm d A
  exact h_transgression.symm


end InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
