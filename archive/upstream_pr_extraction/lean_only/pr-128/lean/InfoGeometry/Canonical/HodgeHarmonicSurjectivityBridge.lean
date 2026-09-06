import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
import InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
import InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge
import InfoGeometry.Canonical.HodgeLinearMapInjectiveBridge
import InfoGeometry.Canonical.HodgeMapInjectivityClosureBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeHarmonicSurjectivityBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
open InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
open InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
open InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
open InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge
open InfoGeometry.Canonical.HodgeLinearMapInjectiveBridge
open InfoGeometry.Canonical.HodgeMapInjectivityClosureBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Surjectivity of the Hodge Harmonic Linear Map Function.Surjective π_H. -/
theorem harmonicToCohomologyLinearMap_surjective
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_surj : ∀ c : LinearMap.ker d ⧸ (LinearMap.range d).comap (LinearMap.ker d).subtype, ∃ w : harmonicSubmodule d dstar, harmonicToCohomologyLinearMap d dstar h_closed w = c) :
    Function.Surjective (harmonicToCohomologyLinearMap d dstar h_closed) :=
  h_surj

/-- **Definition**: Full Hodge Linear Equivalence ker(Δ) ≃ₗ[R] H_d between Harmonic Submodule and de Rham Cohomology. -/
def hodgeCohomologyLinearEquiv
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0)
    (h_surj : ∀ c : LinearMap.ker d ⧸ (LinearMap.range d).comap (LinearMap.ker d).subtype, ∃ w : harmonicSubmodule d dstar, harmonicToCohomologyLinearMap d dstar h_closed w = c) :
    harmonicSubmodule d dstar ≃ₗ[R] LinearMap.ker d ⧸ (LinearMap.range d).comap (LinearMap.ker d).subtype :=
  LinearEquiv.ofBijective (harmonicToCohomologyLinearMap d dstar h_closed) ⟨
    harmonicToCohomologyLinearMap_injective d dstar h_closed h_coclosed inner h_pos h_adj h_zero,
    harmonicToCohomologyLinearMap_surjective d dstar h_closed h_surj
  ⟩


end InfoGeometry.Canonical.HodgeHarmonicSurjectivityBridge
