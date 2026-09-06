import Mathlib.LinearAlgebra.Transvection
import InfoGeometry.Clifford.Cl55WittQuadraticReflection
import InfoGeometry.Clifford.Cl55WittReflectionGeneratedSubgroup

namespace InfoGeometry.Clifford.Clifford55

/-!
# Determinant of an anisotropic split-quadratic reflection

The reflection is a rank-one update of the identity.  Its determinant is
therefore computed with Mathlib's transvection determinant theorem.  No
positive-definite inner product is used here.
-/

noncomputable def quadraticReflectionFunctional
    (v : V55) (_hv : Q55 v ≠ 0) : Module.Dual ℝ V55 where
  toFun x := -(QuadraticMap.polar (⇑Q55) x v / Q55 v)
  map_add' x y := by
    rw [QuadraticMap.polar_add_left, add_div]
    ring
  map_smul' a x := by
    rw [QuadraticMap.polar_smul_left]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring

@[simp] theorem quadraticReflectionFunctional_apply
    (v x : V55) (hv : Q55 v ≠ 0) :
    quadraticReflectionFunctional v hv x =
      -(QuadraticMap.polar (⇑Q55) x v / Q55 v) :=
  rfl

theorem quadraticReflectionLinear_eq_transvection
    (v : V55) (hv : Q55 v ≠ 0) :
    quadraticReflectionLinear v hv =
      LinearMap.transvection (quadraticReflectionFunctional v hv) v := by
  apply LinearMap.ext
  intro x
  rw [quadraticReflectionLinear_apply,
    LinearMap.transvection.apply,
    quadraticReflectionFunctional_apply]
  module

theorem quadraticReflectionLinear_det
    (v : V55) (hv : Q55 v ≠ 0) :
    LinearMap.det (quadraticReflectionLinear v hv) = (-1 : ℝ) := by
  rw [quadraticReflectionLinear_eq_transvection,
    LinearMap.transvection.det,
    quadraticReflectionFunctional_apply,
    QuadraticMap.polar_self]
  field_simp
  ring

theorem quadraticReflection_det
    (v : V55) (hv : Q55 v ≠ 0) :
    (quadraticReflection v hv).det = (-1 : ℝˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  exact quadraticReflectionLinear_det v hv

theorem quadraticReflectionElement_det
    (v : V55) (hv : Q55 v ≠ 0) :
    (quadraticReflectionElement v hv).1.det = (-1 : ℝˣ) := by
  exact quadraticReflection_det v hv

end InfoGeometry.Clifford.Clifford55
