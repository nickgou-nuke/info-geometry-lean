import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.LieDerivativeHomotopyCohomologyZeroBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Lie Derivative of Closed Form is Exact (d ω = 0 → ℒ_X ω = d(ι_X ω) ∈ range d). -/
theorem lie_derivative_closed_form_in_range
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hclosed : d omega = 0) :
    lieDerivativeEnd d iota_X omega = d (iota_X omega) := by
  dsimp [lieDerivativeEnd]
  rw [hclosed, LinearMap.map_zero, add_zero]

/-- **Theorem**: Lie Derivative of Closed Form Lies in Submodule range(d). -/
theorem lie_derivative_closed_mem_range
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hclosed : d omega = 0) :
    lieDerivativeEnd d iota_X omega ∈ LinearMap.range d := by
  rw [lie_derivative_closed_form_in_range d iota_X omega hclosed]
  exact LinearMap.mem_range_self d (iota_X omega)

end InfoGeometry.Canonical.LieDerivativeHomotopyCohomologyZeroBridge
