/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Tower

/-! # A Lorentz-signature subspace of the four-pair split tower

This selects one positive and three negative generators in the native
stage-four quadratic space. It does not construct a spacetime manifold.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl44MinkowskiSubspace

open InfoGeometry.CliffordTower

/-- A chosen four-dimensional subspace of the native split stage. -/
def minkowskiVector (t x y z : ℝ) : SplitSpace 4 :=
  ((t, x), ((0, y), ((0, z), ((0, 0), 0))))

/-- The chosen coordinates are faithfully represented in the split space. -/
theorem minkowskiVector_injective :
    Function.Injective (fun v : ℝ × ℝ × ℝ × ℝ =>
      minkowskiVector v.1 v.2.1 v.2.2.1 v.2.2.2) := by
  rintro ⟨t, x, y, z⟩ ⟨t', x', y', z'⟩ h
  cases h
  rfl

/-- The Lorentz four-plane as a linear map into the native split space. -/
def minkowskiLinear : (Fin 4 → ℝ) →ₗ[ℝ] SplitSpace 4 where
  toFun u := minkowskiVector (u 0) (u 1) (u 2) (u 3)
  map_add' u v := by
    simp [minkowskiVector]
  map_smul' c u := by
    simp [minkowskiVector]

/-- The linear inclusion has no kernel. -/
theorem minkowskiLinear_injective : Function.Injective minkowskiLinear := by
  intro u v h
  have h' : (u 0, u 1, u 2, u 3) = (v 0, v 1, v 2, v 3) := by
    apply minkowskiVector_injective
    exact h
  funext i
  fin_cases i <;> simp_all

/-- The native stage-four quadratic form restricts to signature `(1,3)`. -/
theorem minkowskiVector_quadratic (t x y z : ℝ) :
    Qsplit 4 (minkowskiVector t x y z) = t * t - x * x - y * y - z * z := by
  simp [minkowskiVector, Qsplit, QuadraticMap.prod, Q11_apply,
    InfoGeometry.Clifford.splitQ11_apply]
  ring

/-- The selected native Clifford vector squares to the Minkowski quadratic
form as an element of the full noncommutative stage-four Clifford algebra. -/
theorem minkowskiVector_clifford_square (t x y z : ℝ) :
    CliffordAlgebra.ι (Qsplit 4) (minkowskiVector t x y z) *
      CliffordAlgebra.ι (Qsplit 4) (minkowskiVector t x y z) =
      algebraMap ℝ (Clsplit 4) (t * t - x * x - y * y - z * z) := by
  rw [CliffordAlgebra.ι_sq_scalar, minkowskiVector_quadratic]

/-- The polarized form on the selected four-plane. -/
theorem minkowskiVector_polar (t x y z s a b c : ℝ) :
    QuadraticMap.polar (Qsplit 4) (minkowskiVector t x y z) (minkowskiVector s a b c) =
      2 * (t * s - x * a - y * b - z * c) := by
  simp [QuadraticMap.polar, minkowskiVector, Qsplit, QuadraticMap.prod,
    Q11_apply, InfoGeometry.Clifford.splitQ11_apply]
  ring

/-- The Clifford anticommutator recovers the full polarized Lorentz form,
not only the quadratic values of individual vectors. -/
theorem minkowskiVector_clifford_anticommutator
    (t x y z s a b c : ℝ) :
    CliffordAlgebra.ι (Qsplit 4) (minkowskiVector t x y z) *
        CliffordAlgebra.ι (Qsplit 4) (minkowskiVector s a b c) +
      CliffordAlgebra.ι (Qsplit 4) (minkowskiVector s a b c) *
        CliffordAlgebra.ι (Qsplit 4) (minkowskiVector t x y z) =
      algebraMap ℝ (Clsplit 4) (2 * (t * s - x * a - y * b - z * c)) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, minkowskiVector_polar]

end InfoGeometry.Clifford.Cl44MinkowskiSubspace

end
