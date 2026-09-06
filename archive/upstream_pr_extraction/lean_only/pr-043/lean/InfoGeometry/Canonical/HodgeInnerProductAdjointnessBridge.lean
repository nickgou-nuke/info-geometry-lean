import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
open InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Adjoint Inner Product Inner Sum Identity <(d d* + d* d) ω, ω> = <d* ω, d* ω> + <d ω, d ω>. -/
theorem laplacian_inner_product_sum
    (ip : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V →ₗ[R] R)
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (hadjoint : ∀ (x y : ExteriorAlgebra R V), ip (d x) y = ip (dstar y) x)
    (hadjoint_star : ∀ (x y : ExteriorAlgebra R V), ip (dstar x) y = ip (d y) x)
    (omega : ExteriorAlgebra R V) :
    ip (hodgeDeRhamLaplacian d dstar omega) omega = ip (dstar omega) (dstar omega) + ip (d omega) (d omega) := by
  dsimp [hodgeDeRhamLaplacian]
  rw [LinearMap.map_add, LinearMap.add_apply]
  rw [hadjoint (dstar omega) omega, hadjoint_star (d omega) omega]

end InfoGeometry.Canonical.HodgeInnerProductAdjointnessBridge
