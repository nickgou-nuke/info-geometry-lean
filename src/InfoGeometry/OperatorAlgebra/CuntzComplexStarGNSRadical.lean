/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarGNSState
import InfoGeometry.Cosmology.NonCommutativeHorizonCausalPoset
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! Identify the existing complex pairing radical with the positive quadratic
null set, and descend the actual complex pairing through Mathlib's quotient. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open Archetype_II_GNS_Radical

variable (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)

/-- Null vectors annihilate the full complex pairing, not merely its real part. -/
theorem quotientProduct_null_product (hpos : ∀ i, 0 ≤ q i)
    (x y : ComplexStarCuntzAlg Bool)
    (hx : x ∈ (quotientProductRealState q hq hpos).gnsNullSet) :
    quotientProductFunctional q hq (star x * y) = 0 := by
  have hre := (quotientProductRealState q hq hpos).state_null_product_zero y x hx
  have him := (quotientProductRealState q hq hpos).state_null_product_zero
    (Complex.I • y) x hx
  change (quotientProductFunctional q hq (star x * y)).re = 0 at hre
  change (quotientProductFunctional q hq (star x * (Complex.I • y))).re = 0 at him
  rw [mul_smul_comm, map_smul] at him
  simp only [smul_eq_mul, Complex.I_mul_re] at him
  apply Complex.ext
  · exact hre
  · exact neg_eq_zero.mp him

/-- The generic complex radical and the real quadratic null set coincide. -/
theorem quotientProduct_radical_iff (hpos : ∀ i, 0 ≤ q i)
    (x : ComplexStarCuntzAlg Bool) :
    x ∈ gnsRadical (quotientProductFunctional q hq) ↔
      x ∈ (quotientProductRealState q hq hpos).gnsNullSet := by
  constructor
  · intro hx
    exact (quotientProductRealState_null_iff q hq hpos x).mpr (hx x)
  · intro hx y
    have h := quotientProduct_null_product q hq hpos x y hx
    have hs := quotientProductFunctional_star q hq (star x * y)
    simpa only [star_mul, star_star, h, star_zero] using hs

/-- The positive quotient functional's genuine complex sesquilinear pairing. -/
def quotientProductPairing :
    ComplexStarCuntzAlg Bool →ₛₗ[starRingEnd ℂ]
      ComplexStarCuntzAlg Bool →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => quotientProductFunctional q hq (star x * y)
      map_add' := by intro y z; simp only [mul_add, map_add]
      map_smul' := by intro c y; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change quotientProductFunctional q hq (star (x + y) * z) =
      quotientProductFunctional q hq (star x * z) +
        quotientProductFunctional q hq (star y * z)
    simp only [star_add, add_mul, map_add]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change quotientProductFunctional q hq (star (c • x) * y) =
      star c • quotientProductFunctional q hq (star x * y)
    simp only [star_complex_smul, smul_mul_assoc, map_smul]

theorem quotientProductPairing_hermitian (x y : ComplexStarCuntzAlg Bool) :
    quotientProductPairing q hq x y = star (quotientProductPairing q hq y x) := by
  change quotientProductFunctional q hq (star x * y) =
    star (quotientProductFunctional q hq (star y * x))
  have h := quotientProductFunctional_star q hq (star y * x)
  simpa only [star_mul, star_star] using h

/-- Descent uses the existing radical; it does not assert a Hilbert completion. -/
def quotientProductPairingDescended :
    (ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq))
      →ₛₗ[starRingEnd ℂ]
    (ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) →ₗ[ℂ] ℂ :=
  (quotientProductPairing q hq).liftQ₂
    (gnsRadical (quotientProductFunctional q hq))
    (gnsRadical (quotientProductFunctional q hq))
    (by
      intro x hx
      apply LinearMap.ext
      intro y
      change quotientProductPairing q hq x y = 0
      rw [quotientProductPairing_hermitian]
      change star (quotientProductFunctional q hq (star y * x)) = 0
      rw [hx y, star_zero])
    (by
      intro x hx
      apply LinearMap.ext
      intro y
      exact hx y)

@[simp] theorem quotientProductPairingDescended_mk (x y : ComplexStarCuntzAlg Bool) :
    quotientProductPairingDescended q hq (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = quotientProductFunctional q hq (star x * y) := rfl

open scoped ComplexOrder in
/-- Positivity survives descent to the native complex quotient. -/
theorem quotientProductPairingDescended_nonneg (hpos : ∀ i, 0 ≤ q i)
    (z : ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) :
    0 ≤ quotientProductPairingDescended q hq z z := by
  refine Quotient.inductionOn z ?_
  intro x
  exact quotientProductFunctional_nonneg q hq hpos x

/-- Quotienting by the radical removes exactly the quadratic degeneracy. -/
theorem quotientProductPairingDescended_eq_zero_iff (hpos : ∀ i, 0 ≤ q i)
    (z : ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) :
    quotientProductPairingDescended q hq z z = 0 ↔ z = 0 := by
  refine Quotient.inductionOn z ?_
  intro x
  change quotientProductFunctional q hq (star x * x) = 0 ↔
    (Submodule.Quotient.mk x :
      ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) = 0
  rw [Submodule.Quotient.mk_eq_zero, quotientProduct_radical_iff q hq hpos,
    quotientProductRealState_null_iff q hq hpos]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
