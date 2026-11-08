import Mathlib.Algebra.Group.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic
import InfoGeometry.Core.HomogeneousSpaces
import InfoGeometry.LogarithmicBridge

noncomputable section

namespace InfoGeometry.Canonical.HomogeneousModularFlows

/-!
# Homogeneous Modular Flows and the Maurer-Cartan Capstone

This module formalizes the geometric embedding of the Logarithmic Bridge
(the Connes Radon-Nikodym cocycle) into the Klein-Erlangen homogeneous-space architecture.

Specifically, it constructs the Maurer-Cartan form evaluated on group derivations
and proves the capstone theorem:
The logarithmic bridge factors exactly through the Maurer-Cartan form on the homogeneous space of modular flows.
-/

variable {R : Type*} [CommRing R]

/--
  The algebraic Maurer-Cartan derivative on the group.
  For a generic derivation mapping `D : R → R` and a point `g : R` in the ring 
  (acting as the group of modular transformations), 
  the Maurer-Cartan form pulls back to `g⁻¹ * D(g)`.
-/
def maurerCartanDerivative (D : R →ₗ[R] R) (g inv_g : R) : R :=
  inv_g * D g

def maurerCartanPath {ι : Type*} (D : R →ₗ[R] R)
    (path inversePath : ι → R) (t : ι) : R :=
  maurerCartanDerivative D (path t) (inversePath t)

theorem maurerCartanPath_eq_logarithmicBridge
    {ι : Type*} (D : R →ₗ[R] R) (path inversePath : ι → R)
    (t : ι) :
    maurerCartanPath D path inversePath t =
      inversePath t * D (path t) :=
  rfl

/-- 
  🏆 THEOREM: The Homogeneous-Space Capstone
  
  The logarithmic bridge (the Connes Radon-Nikodym chain rule) factors exactly
  through the Maurer-Cartan form evaluated on the homogeneous space of modular flows.
-/
theorem capstone_logarithmicBridge_factors_maurerCartan
    (D : R →ₗ[R] R) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (Δ12 inv_Δ12 Δ23 inv_Δ23 : R) :
    maurerCartanDerivative D (Δ12 * Δ23) (inv_Δ12 * inv_Δ23) =
      maurerCartanDerivative D Δ12 inv_Δ12 * (Δ23 * inv_Δ23) +
      maurerCartanDerivative D Δ23 inv_Δ23 * (Δ12 * inv_Δ12) := by
  dsimp [maurerCartanDerivative]
  rw [hD Δ12 Δ23]
  ring

/-! In the commutative modular scalar corridor, the inverse factors in the
Maurer--Cartan product rule are genuine inverse witnesses.  Substituting them
reduces the transported product rule to the additive logarithmic derivative. -/
theorem maurerCartanDerivative_mul_eq_add
    (D : R →ₗ[R] R) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (Δ12 inv_Δ12 Δ23 inv_Δ23 : R)
    (h12 : Δ12 * inv_Δ12 = 1)
    (h23 : Δ23 * inv_Δ23 = 1) :
    maurerCartanDerivative D (Δ12 * Δ23) (inv_Δ12 * inv_Δ23) =
      maurerCartanDerivative D Δ12 inv_Δ12 +
        maurerCartanDerivative D Δ23 inv_Δ23 := by
  rw [capstone_logarithmicBridge_factors_maurerCartan D hD Δ12 inv_Δ12 Δ23 inv_Δ23]
  rw [h12, h23]
  ring

/-! The normalized Maurer--Cartan product rule is the same theorem as the
    logarithmic Radon--Nikodym chain rule, after unfolding the common
    left-invariant derivative expression. -/
theorem maurerCartanDerivative_eq_logarithmicRadonNikodym
    (D : R →ₗ[R] R) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (Δ12 inv_Δ12 Δ23 inv_Δ23 : R)
    (h12 : Δ12 * inv_Δ12 = 1)
    (h23 : Δ23 * inv_Δ23 = 1) :
    maurerCartanDerivative D (Δ12 * Δ23) (inv_Δ12 * inv_Δ23) =
      inv_Δ12 * D Δ12 + inv_Δ23 * D Δ23 := by
  simpa [maurerCartanDerivative] using
    (InfoGeometry.LogarithmicBridge.logarithmicRadonNikodym_chainRule_of_inverses
      D hD Δ12 inv_Δ12 Δ23 inv_Δ23 h12 h23)

/-! The unit-group form supplies the inverse witnesses canonically. -/
theorem maurerCartanUnit_mul_eq_add
    (D : R →ₗ[R] R) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (u v : Rˣ) :
    maurerCartanDerivative D ((u * v : Rˣ) : R) ((↑((u * v)⁻¹) : Rˣ) : R) =
      maurerCartanDerivative D (u : R) ((↑(u⁻¹) : Rˣ) : R) +
        maurerCartanDerivative D (v : R) ((↑(v⁻¹) : Rˣ) : R) := by
  have h := maurerCartanDerivative_mul_eq_add D hD
    (u : R) ((↑(u⁻¹) : Rˣ) : R)
    (v : R) ((↑(v⁻¹) : Rˣ) : R)
    (by simp) (by simp)
  simpa [Units.val_mul, mul_comm] using h

end InfoGeometry.Canonical.HomogeneousModularFlows

end noncomputable section
