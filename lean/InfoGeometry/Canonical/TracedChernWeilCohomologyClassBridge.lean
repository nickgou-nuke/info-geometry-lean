import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- **Definition**: Traced Chern-Weil Cohomology Class [Tr(F ∧ F)] ∈ H_d = ker d / range d. -/
def tracedChernWeilCohomologyClass
    (d : Module.End R (ExteriorAlgebra R V))
    (F2 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_closed : matrixExteriorDerivative d F2 = 0) : deRhamCohomologyModule d :=
  Submodule.Quotient.mk ⟨matrixTraceForm F2, matrix_traced_curvature_square_closed d F2 h_closed⟩

/-- **Theorem**: Invariance of Traced Chern-Weil Class Under Exact Curvature Deformations [Tr(F²) + d ω] = [Tr(F²)]. -/
theorem traced_chern_weil_class_exact_invariance
    (d : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0)
    (F2 : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_closed : matrixExteriorDerivative d F2 = 0)
    (omega : ExteriorAlgebra R V) :
    Submodule.Quotient.mk (p := (LinearMap.range d).comap (LinearMap.ker d).subtype)
      ⟨matrixTraceForm F2 + d omega, by
        rw [LinearMap.mem_ker]
        rw [LinearMap.map_add]
        have h1 : d (matrixTraceForm F2) = 0 := matrix_traced_curvature_square_closed d F2 h_closed
        have h2 : d (d omega) = 0 := LinearMap.congr_fun hd2 omega
        rw [h1, h2, add_zero]⟩ =
    (tracedChernWeilCohomologyClass d F2 h_closed) := by
  dsimp [tracedChernWeilCohomologyClass]
  rw [Submodule.Quotient.eq]
  rw [Submodule.mem_comap]
  dsimp [Submodule.subtype]
  use omega
  abel

end InfoGeometry.Canonical.TracedChernWeilCohomologyClassBridge
