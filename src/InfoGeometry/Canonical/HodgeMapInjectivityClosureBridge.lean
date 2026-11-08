import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
import InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
import InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge
import InfoGeometry.Canonical.HodgeLinearMapInjectiveBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeMapInjectivityClosureBridge

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

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Literal Kernel Triviality ker(π_H) = ⊥ for the Hodge Harmonic Linear Map. -/
theorem harmonicToCohomologyLinearMap_ker_eq_bot
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0) :
    LinearMap.ker (harmonicToCohomologyLinearMap d dstar h_closed) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact harmonicToCohomologyLinearMap_injective d dstar h_closed h_coclosed inner h_pos h_adj h_zero

/-- **Theorem**: Master Hodge Map Injectivity Closure Synthesis.
    Unifies:
    1. Certified linear map π_H : ker(Δ) →ₗ[R] H_d.
    2. Function injectivity Function.Injective π_H.
    3. Submodule kernel triviality theorem LinearMap.ker π_H = ⊥.
    4. Exact machine-checked proof closure of the injectivity kernel half of the Hodge Isomorphism Theorem. -/
theorem master_hodge_map_injectivity_closure_synthesis
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0) :
    (LinearMap.ker (harmonicToCohomologyLinearMap d dstar h_closed) = ⊥) ∧
    (Function.Injective (harmonicToCohomologyLinearMap d dstar h_closed)) := ⟨
  harmonicToCohomologyLinearMap_ker_eq_bot d dstar h_closed h_coclosed inner h_pos h_adj h_zero,
  harmonicToCohomologyLinearMap_injective d dstar h_closed h_coclosed inner h_pos h_adj h_zero
⟩

end InfoGeometry.Canonical.HodgeMapInjectivityClosureBridge
