import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
import InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge
import InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
open InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
open InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Harmonic Exact Form Zero Theorem (Injectivity Core of Hodge Theory).
    If a form w is both harmonic d* w = 0 and exact w = d α,
    and the inner product satisfies ⟨d α, w⟩ = ⟨α, d* w⟩ and positive definiteness ⟨w, w⟩ = 0 → w = 0,
    then w = 0. -/
theorem harmonic_exact_zero
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0)
    (alpha w : ExteriorAlgebra R V)
    (h_exact : w = d alpha)
    (h_cocclosed : dstar w = 0) :
    w = 0 := by
  have h_inner : inner w w = 0 := by
    nth_rw 1 [h_exact]
    rw [h_adj alpha w]
    rw [h_cocclosed]
    exact h_zero alpha
  exact h_pos w h_inner

end InfoGeometry.Canonical.HodgeHarmonicInjectivityBridge
