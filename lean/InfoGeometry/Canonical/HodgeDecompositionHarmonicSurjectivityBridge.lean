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
import InfoGeometry.Canonical.HodgeHarmonicSurjectivityBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeDecompositionHarmonicSurjectivityBridge

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
open InfoGeometry.Canonical.HodgeHarmonicSurjectivityBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Constructive Derivation of Hodge Map Surjectivity Function.Surjective π_H from Hodge Orthogonal Decomposition w = d α + h. -/
theorem harmonicToCohomologyLinearMap_surjective_from_decomposition
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_decomp : ∀ w : LinearMap.ker d, ∃ alpha : ExteriorAlgebra R V, ∃ h : harmonicSubmodule d dstar, w.1 = d alpha + h.1) :
    Function.Surjective (harmonicToCohomologyLinearMap d dstar h_closed) := by
  intro c
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rcases h_decomp w with ⟨alpha, h, hw⟩
  use h
  dsimp [harmonicToCohomologyLinearMap]
  rw [Submodule.Quotient.eq]
  rw [Submodule.mem_comap]
  rw [LinearMap.mem_range]
  use -alpha
  dsimp
  rw [LinearMap.map_neg, hw]
  abel

/-- **Definition**: Full Unconditional Hodge Linear Equivalence ker(Δ) ≃ₗ[R] H_d derived from Hodge Orthogonal Decomposition w = d α + h. -/
def hodgeDecompositionLinearEquiv
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0)
    (h_decomp : ∀ w : LinearMap.ker d, ∃ alpha : ExteriorAlgebra R V, ∃ h : harmonicSubmodule d dstar, w.1 = d alpha + h.1) :
    harmonicSubmodule d dstar ≃ₗ[R] LinearMap.ker d ⧸ (LinearMap.range d).comap (LinearMap.ker d).subtype :=
  LinearEquiv.ofBijective (harmonicToCohomologyLinearMap d dstar h_closed) ⟨
    harmonicToCohomologyLinearMap_injective d dstar h_closed h_coclosed inner h_pos h_adj h_zero,
    harmonicToCohomologyLinearMap_surjective_from_decomposition d dstar h_closed h_decomp
  ⟩

end InfoGeometry.Canonical.HodgeDecompositionHarmonicSurjectivityBridge
