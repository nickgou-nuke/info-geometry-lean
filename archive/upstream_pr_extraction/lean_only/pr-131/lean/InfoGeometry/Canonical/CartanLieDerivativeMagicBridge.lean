import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CartanLieDerivativeMagicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Cartan's Lie Derivative Operator L_X = d ∘ ι_X + ι_X ∘ d. -/
def lieDerivative (d iota_X : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V) (omega : ExteriorAlgebra R V) : ExteriorAlgebra R V :=
  d (iota_X omega) + iota_X (d omega)

/-- **Definition**: Lie Derivative Endomorphism in Module.End R (ExteriorAlgebra R V). -/
def lieDerivativeEnd (d iota_X : Module.End R (ExteriorAlgebra R V)) : Module.End R (ExteriorAlgebra R V) :=
  d.comp iota_X + iota_X.comp d

/-- **Theorem**: Lie Derivative Commutes with Exterior Derivative (d ∘ L_X = L_X ∘ d) under d² = 0. -/
theorem lie_derivative_commutes_exterior_derivative
    (d iota_X : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V)
    (hd2 : ∀ x, d (d x) = 0) (omega : ExteriorAlgebra R V) :
    d (lieDerivative d iota_X omega) = lieDerivative d iota_X (d omega) := by
  dsimp [lieDerivative]
  rw [map_add, hd2 (iota_X omega), zero_add, hd2 omega, map_zero, add_zero]

/-- **Theorem**: Lie Derivative Endomorphism Commutes with Exterior Derivative (d ∘ L_X = L_X ∘ d) in Module.End. -/
theorem lieDerivative_commutes_exteriorDerivative_end
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0) :
    d.comp (lieDerivativeEnd d iota_X) = (lieDerivativeEnd d iota_X).comp d := by
  ext omega
  simp only [lieDerivativeEnd, LinearMap.add_apply, LinearMap.comp_apply]
  have h_d_sq : ∀ x, d (d x) = 0 := fun x => LinearMap.congr_fun hd2 x
  rw [LinearMap.map_add, h_d_sq (iota_X omega), zero_add, h_d_sq omega, LinearMap.map_zero, add_zero]


end InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
