import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeQuotientModuleIsomorphismBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
open InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
open InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Harmonic Form Cohomology Class Projection Map π_H : ker(Δ) → H_d = ker d / range d. -/
def harmonicToCohomologyClassMap
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (w_harmonic : harmonicSubmodule d dstar)
    (hclosed : d w_harmonic.1 = 0) : deRhamCohomologyModule d :=
  Submodule.Quotient.mk ⟨w_harmonic.1, harmonic_is_closed d w_harmonic.1 hclosed⟩

/-- **Theorem**: Harmonic Form Zero Cohomology Class Map Normalization. -/
theorem harmonic_zero_class_eq_zero
    (d : Module.End R (ExteriorAlgebra R V)) :
    Submodule.Quotient.mk (p := (LinearMap.range d).comap (LinearMap.ker d).subtype)
      ⟨0, LinearMap.map_zero d⟩ = (Submodule.Quotient.mk 0 : deRhamCohomologyModule d) :=
  rfl

end InfoGeometry.Canonical.HodgeQuotientModuleIsomorphismBridge
