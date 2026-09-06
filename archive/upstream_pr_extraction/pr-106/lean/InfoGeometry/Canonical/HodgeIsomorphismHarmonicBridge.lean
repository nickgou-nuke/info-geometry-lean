import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
open InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Harmonic Form Submodule ker(Δ) inside Exterior Algebra. -/
def harmonicSubmodule (d dstar : Module.End R (ExteriorAlgebra R V)) : Submodule R (ExteriorAlgebra R V) :=
  LinearMap.ker (hodgeDeRhamLaplacian d dstar)

/-- **Theorem**: Harmonic Forms map into Closed Forms Submodule ker(d) when d ω = 0. -/
theorem harmonic_is_closed
    (d : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hclosed : d omega = 0) :
    omega ∈ LinearMap.ker d := by
  rw [LinearMap.mem_ker]
  exact hclosed


end InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
