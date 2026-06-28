import Mathlib
import InfoGeometry.Canonical.CPTCstarStateLimit

/-!
# Inductive Limit of GNS Hilbert Spaces

Finite-stage GNS inner-product transport over the existing tensor tower.
The theorem below proves that a compatible family of finite-stage functionals
makes the one-step bonding map preserve the algebraic GNS inner product.
-/

namespace InfoGeometry.Canonical.GNSHilbertColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CPTCstarStateLimit

universe u

/-!
## Directed System of Local GNS Spaces
-/

/-- 
The local GNS inner product proxy at finite stage n.
Defined canonically as: `⟨x, y⟩_n = ω_n(x^* y)`
-/
def local_inner_product (ω : ∀ n, FiniteStageFunctional n) (n : ℕ) (x y : Stage n) : ℝ :=
  (ω n).func (star x * y)

/-- The bonding map preserves the involution since it acts as A ⊗ I_2. -/
theorem bond_star (n : ℕ) (A : Stage n) : stageBond n (star A) = star (stageBond n A) := by
  ext i j
  simp [stageBond, stageEmbed_apply, matStageEmbed, Matrix.star_apply, Matrix.one_apply]
  congr 1
  aesop

/-!
## Isometric Transition Theorem
-/

/-- Compatible finite-stage functionals make the bonding map preserve the local
GNS inner product. -/
theorem transition_is_isometry 
    (ω : ∀ n, FiniteStageFunctional n)
    (h_compat : IsCompatibleFunctionalFamily ω)
    (n : ℕ) (x y : Stage n) :
    local_inner_product ω (n + 1) (stageBond n x) (stageBond n y) = 
      local_inner_product ω n x y := by
  dsimp [local_inner_product]
  have h1 : star (stageBond n x) = stageBond n (star x) := (bond_star n x).symm
  have h2 : stageBond n (star x) * stageBond n y = stageBond n (star x * y) := by
    change matStageEmbed n (star x) * matStageEmbed n y = matStageEmbed n (star x * y)
    rw [← matStageEmbed_mul]
  have h_mul : star (stageBond n x) * stageBond n y = stageBond n (star x * y) := by
    rw [h1, h2]
  -- we know the target has `star (matStageEmbed n x) * matStageEmbed n y`
  -- and `stageBond` is `matStageEmbed` definitionally.
  -- we can just rewrite using h_mul, but we need to change it exactly to the target
  change (ω (n + 1)).func (star (stageBond n x) * stageBond n y) = (ω n).func (star x * y)
  rw [h_mul]
  exact h_compat n (star x * y)

end InfoGeometry.Canonical.GNSHilbertColimit
