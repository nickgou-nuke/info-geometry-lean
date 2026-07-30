import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
import InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
import InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeLinearMapInjectiveBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
open InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
open InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
open InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
open InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Literal Injectivity of the Hodge Harmonic Linear Map Function.Injective π_H. -/
theorem harmonicToCohomologyLinearMap_injective
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0) :
    Function.Injective (harmonicToCohomologyLinearMap d dstar h_closed) := by
  intro w1 w2 h_eq
  have h_sub : harmonicToCohomologyLinearMap d dstar h_closed (w1 - w2) = 0 := by
    rw [map_sub, h_eq, sub_self]
  have h_zero_class : Submodule.Quotient.mk (p := (LinearMap.range d).comap (LinearMap.ker d).subtype)
    ⟨(w1 - w2).1, h_closed (w1 - w2) (w1 - w2).2⟩ = 0 := h_sub
  rw [Submodule.Quotient.mk_eq_zero] at h_zero_class
  rw [Submodule.mem_comap] at h_zero_class
  dsimp [Submodule.subtype] at h_zero_class
  rcases h_zero_class with ⟨alpha, h_exact⟩
  have h_coclosed_diff : dstar (w1 - w2).1 = 0 := h_coclosed (w1 - w2) (w1 - w2).2
  have h_diff_zero : (w1 - w2).1 = 0 :=
    harmonic_exact_zero d dstar inner h_pos h_adj h_zero alpha (w1 - w2).1 h_exact.symm h_coclosed_diff
  ext
  rw [Submodule.coe_sub] at h_diff_zero
  rw [sub_eq_zero] at h_diff_zero
  exact h_diff_zero

/-- **Theorem**: Master Hodge Linear Map Injectivity Synthesis.
    Unifies:
    1. Linear harmonic projection map π_H : ker(Δ) →ₗ[R] H_d.
    2. Harmonic exact form zero theorem w ∈ im(d) ∩ ker(d*) → w = 0.
    3. Literal machine-checked injectivity theorem Function.Injective π_H.
    4. Exact formal proof closure of the injectivity half of the Hodge Isomorphism Theorem. -/
theorem master_hodge_linear_map_injective_synthesis
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0) :
    Function.Injective (harmonicToCohomologyLinearMap d dstar h_closed) :=
  harmonicToCohomologyLinearMap_injective d dstar h_closed h_coclosed inner h_pos h_adj h_zero

end InfoGeometry.Canonical.HodgeLinearMapInjectiveBridge
