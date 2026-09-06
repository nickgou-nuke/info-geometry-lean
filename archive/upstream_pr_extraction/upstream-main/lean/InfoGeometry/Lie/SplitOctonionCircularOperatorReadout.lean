import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Circular coordinate operators

Native left and right multiplication transported through the circular
Peirce coordinate equivalence.  Matrix and flow readouts are downstream
owners; this file contains only the reusable linear-operator transport.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

abbrev Coord := Fin 8 → ℝ

noncomputable def circularCoordinateLinearEquiv : CanonicalZorn ≃ₗ[ℝ] Coord :=
  circularPeirceBasis.equivFun

noncomputable def circularOperatorReadout :
    Module.End ℝ CanonicalZorn ≃ₐ[ℝ] Module.End ℝ Coord :=
  circularCoordinateLinearEquiv.conjAlgEquiv ℝ

noncomputable def L (a : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun x := InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul a x
  map_add' x y := zMul_add_right a x y
  map_smul' c x := zMul_smul_right c a x

noncomputable def R (a : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun x := InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul x a
  map_add' x y := zMul_add_left x y a
  map_smul' c x := zMul_smul_left c x a

@[simp] theorem L_apply (a x : CanonicalZorn) : L a x = a * x := rfl
@[simp] theorem R_apply (a x : CanonicalZorn) : R a x = x * a := rfl

noncomputable def circularL (a : CanonicalZorn) : Module.End ℝ Coord :=
  circularOperatorReadout (L a)

noncomputable def circularR (a : CanonicalZorn) : Module.End ℝ Coord :=
  circularOperatorReadout (R a)

@[simp] theorem circularL_apply (a : CanonicalZorn) (x : Coord) :
    circularL a x = circularCoordinateLinearEquiv
      (a * circularCoordinateLinearEquiv.symm x) := by
  simp [circularL, circularOperatorReadout,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

@[simp] theorem circularR_apply (a : CanonicalZorn) (x : Coord) :
    circularR a x = circularCoordinateLinearEquiv
      (circularCoordinateLinearEquiv.symm x * a) := by
  simp [circularR, circularOperatorReadout,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

theorem circularL_on_basis (a : CanonicalZorn) (i : Fin 8) :
    circularL a (circularCoordinateLinearEquiv (circularPeirceBasis i)) =
      circularCoordinateLinearEquiv (a * circularPeirceBasis i) := by
  rw [circularL_apply]
  simp

theorem circularR_on_basis (a : CanonicalZorn) (i : Fin 8) :
    circularR a (circularCoordinateLinearEquiv (circularPeirceBasis i)) =
    circularCoordinateLinearEquiv (circularPeirceBasis i * a) := by
  rw [circularR_apply]
  simp

noncomputable def circularMatrix : Module.End ℝ Coord ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))

end InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
