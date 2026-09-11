import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwelveFoldAdditiveCharacter

/-!
# The twelvefold root on the analytic circle

This owner connects the existing primitive complex phase to Mathlib's `Circle`
and to the finite subgroup `rootsOfUnity 12 ℂ`.  The additive character and
the Dirichlet characters remain separate owners: this file only supplies the
circle/torsion realization.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldCircleCyclotomic

open InfoGeometry.Canonical.TwelveFoldAdditiveCharacter

/-- The primitive twelvefold phase, regarded as a point of the unit circle. -/
def zeta12Circle : Circle :=
  ⟨zeta12, by
    change zeta12 ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    unfold zeta12
    rw [Complex.norm_exp]
    simp
  ⟩

@[simp] theorem zeta12Circle_coe : (zeta12Circle : ℂ) = zeta12 := by
  change zeta12 = zeta12
  rfl

/-- The circle point maps to a unit in the complex multiplicative group. -/
def zeta12CircleUnit : ℂˣ := Circle.toUnits zeta12Circle

theorem circle_toUnits_injective : Function.Injective Circle.toUnits := by
  intro a b h
  apply Circle.ext
  have hv := congrArg Units.val h
  simpa [Circle.toUnits_apply] using hv

/-- The circle generator is primitive as a complex unit. -/
theorem zeta12CircleUnit_primitive : IsPrimitiveRoot zeta12CircleUnit 12 := by
  refine IsPrimitiveRoot.mk ?_ ?_
  · apply Units.ext
    simpa [zeta12CircleUnit, Circle.toUnits_apply, zeta12Circle_coe] using
      zeta12_pow_twelve
  · intro l hl
    apply zeta12_primitive.dvd_of_pow_eq_one l
    have hv := congrArg Units.val hl
    simpa [zeta12CircleUnit, Circle.toUnits_apply, zeta12Circle_coe] using hv

theorem zeta12CircleUnit_mem_rootsOfUnity :
    zeta12CircleUnit ∈ rootsOfUnity 12 ℂ :=
  zeta12CircleUnit_primitive.mem_rootsOfUnity

theorem rootsOfUnity_twelve_isCyclic : IsCyclic (rootsOfUnity 12 ℂ) := by
  letI : NeZero (12 : ℕ) := ⟨by norm_num⟩
  exact rootsOfUnity.isCyclic ℂ 12

theorem circle_generator_coe_eq_additive_generator :
    (zeta12CircleUnit : ℂ) = additiveCharacter12 1 := by
  change (zeta12Circle : ℂ) = additiveCharacter12 1
  rw [zeta12Circle_coe]
  exact (additiveCharacter12_value_one).symm

end InfoGeometry.Canonical.TwelveFoldCircleCyclotomic
