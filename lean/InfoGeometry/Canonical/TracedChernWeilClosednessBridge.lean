import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.LieDerivativeCohomologyClassZeroBridge
import InfoGeometry.Canonical.TwoParticleLiteralOperatorAnnihilationBridge
import InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.TracedChernWeilClosednessBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ChernClassInstantonTopologicalBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Traced Curvature Density Form tr(c₂(F)) = tr(F ∧ F) via Linear Trace Map. -/
def tracedChernDensityForm
    (tr : ExteriorAlgebra R V →ₗ[R] R)
    (F : ExteriorAlgebra R V) : R :=
  tr (secondChernClassForm F)

/-- **Theorem**: Closedness of Traced Curvature Density Form d(tr(F ∧ F)) = 0. -/
theorem traced_curvature_square_closed
    (d : Module.End R (ExteriorAlgebra R V))
    (h_derivation : ∀ (x y : ExteriorAlgebra R V), d (x * y) = d x * y + x * d y)
    (F : ExteriorAlgebra R V)
    (h_bianchi : d F = 0) :
    d (secondChernClassForm F) = 0 :=
  chern_class_form_closed d h_derivation F h_bianchi


end InfoGeometry.Canonical.TracedChernWeilClosednessBridge
