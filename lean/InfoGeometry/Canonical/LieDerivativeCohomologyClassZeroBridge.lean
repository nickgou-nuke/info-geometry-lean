import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.LieDerivativeHomotopyCohomologyZeroBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.LieDerivativeCohomologyClassZeroBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.LieDerivativeHomotopyCohomologyZeroBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Quotient Map Sends Lie Derivative of Closed Form to Zero in de Rham Cohomology Module H = ker(d) / range(d). -/
theorem lie_derivative_cohomology_class_eq_zero
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0)
    (w : LinearMap.ker d) :
    Submodule.Quotient.mk (p := (LinearMap.range d).comap (LinearMap.ker d).subtype)
      ⟨lieDerivativeEnd d iota_X w.1, by
        rw [LinearMap.mem_ker]
        have h1 : d (lieDerivativeEnd d iota_X w.1) = lieDerivativeEnd d iota_X (d w.1) := by
          have h_comp := LinearMap.congr_fun (lieDerivative_commutes_exteriorDerivative_end d iota_X hd2) w.1
          exact h_comp
        rw [h1]
        have hw_zero : d w.1 = 0 := w.2
        rw [hw_zero, LinearMap.map_zero]⟩ = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  rw [Submodule.mem_comap]
  dsimp [Submodule.subtype]
  exact lie_derivative_closed_mem_range d iota_X w.1 w.2

end InfoGeometry.Canonical.LieDerivativeCohomologyClassZeroBridge
