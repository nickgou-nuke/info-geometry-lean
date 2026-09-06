import InfoGeometry.Physics.ZornScalingFlow
import InfoGeometry.Canonical.ThreeColorCyclotomicChargeProjectors

/-!
# Sixth-root Zorn scaling and cubic charge

This owner packages the existing Zorn scaling theorem

* `p^6 = 1`  ⇒  `((p : ℂ)^2)^3 = 1`

with the native cubic charge projector calculus on `ZornMatrix`.
It does not introduce a separate cover object; it only records the
order-3 quotient action already proved by the existing owners.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

/-- The effective weight induced by a sixth-root Zorn scaling is a cube root. -/
theorem zornSixthRoot_effectiveCubeRoot
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    ((p : ℂ) ^ 2) ^ 3 = 1 :=
  InfoGeometry.Physics.ZornScalingFlow.automorphic_zornScale_effective_cube_root p hp

/-- The cubic charge at the effective Zorn weight has order three. -/
theorem cubicCharge_of_sixthRoot
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (cubicCharge ((p : ℂ) ^ 2)).comp
        ((cubicCharge ((p : ℂ) ^ 2)).comp (cubicCharge ((p : ℂ) ^ 2))) =
      LinearMap.id := by
  simpa using
    cubicCharge_pow_three ((p : ℂ) ^ 2)
      (zornSixthRoot_effectiveCubeRoot p hp)

/-- The three native cyclotomic projectors remain a partition of the identity. -/
theorem cubicProjectors_sum_of_sixthRoot
    (Z : ZornMatrix ℂ) :
    cubicProjectorZero Z + cubicProjectorPlus Z + cubicProjectorMinus Z = Z := by
  exact cubicProjectors_sum_eq_id Z

end InfoGeometry.Canonical
