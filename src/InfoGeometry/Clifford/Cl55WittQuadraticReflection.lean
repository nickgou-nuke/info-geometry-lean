import InfoGeometry.Clifford.Cl55WittOrthogonalNative
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native reflections for the split Witt quadratic form

This file defines the ordinary quadratic reflection attached to an
anisotropic vector using Mathlib's `QuadraticMap.IsometryEquiv` interface.
It deliberately proves only the reflection itself; Cartan--Dieudonné
generation and the Pin covering theorem remain separate statements.
-/

noncomputable def quadraticReflectionLinear
    (v : V55) (hv : Q55 v ≠ 0) : V55 →ₗ[ℝ] V55 :=
  InfoGeometry.Clifford.realQuadraticReflectionLinear Q55 v hv

theorem quadraticReflectionLinear_apply
    (v x : V55) (hv : Q55 v ≠ 0) :
    quadraticReflectionLinear v hv x =
      x - (QuadraticMap.polar (⇑Q55) x v / Q55 v) • v :=
  rfl

theorem quadraticReflectionLinear_involutive
    (v : V55) (hv : Q55 v ≠ 0) :
    Function.Involutive (quadraticReflectionLinear v hv) := by
  exact InfoGeometry.Clifford.realQuadraticReflectionLinear_involutive Q55 v hv

noncomputable def quadraticReflection
    (v : V55) (hv : Q55 v ≠ 0) : V55 ≃ₗ[ℝ] V55 :=
  InfoGeometry.Clifford.realQuadraticReflection Q55 v hv

theorem quadraticReflection_apply
    (v x : V55) (hv : Q55 v ≠ 0) :
    quadraticReflection v hv x =
      x - (QuadraticMap.polar (⇑Q55) x v / Q55 v) • v :=
  rfl

theorem quadraticReflection_apply_self
    (v : V55) (hv : Q55 v ≠ 0) :
    quadraticReflection v hv v = -v := by
  rw [quadraticReflection_apply, QuadraticMap.polar_self]
  change v - ((2 : ℕ) • Q55 v / Q55 v) • v = -v
  have hscalar : (2 : ℕ) • Q55 v / Q55 v = (2 : ℝ) := by
    simp only [two_nsmul, add_div, div_self hv, one_add_one_eq_two]
  rw [hscalar]
  module



theorem quadraticReflection_apply_of_polar_eq_zero
    (v x : V55) (hv : Q55 v ≠ 0)
    (horth : QuadraticMap.polar (⇑Q55) x v = 0) :
    quadraticReflection v hv x = x := by
  rw [quadraticReflection_apply, horth, zero_div, zero_smul, sub_zero]

noncomputable def quadraticReflection_isometry
    (v : V55) (hv : Q55 v ≠ 0) :
    Q55.IsometryEquiv Q55 :=
  InfoGeometry.Clifford.realQuadraticReflectionIsometry Q55 v hv

noncomputable def quadraticReflectionIsometry
    (v : V55) (hv : Q55 v ≠ 0) : Q55.IsometryEquiv Q55 :=
  quadraticReflection_isometry v hv

end InfoGeometry.Clifford.Clifford55
