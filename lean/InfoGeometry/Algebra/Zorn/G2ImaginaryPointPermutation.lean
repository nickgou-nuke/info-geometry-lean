import InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction

/-!
# Discrete permutation interface for the 63-point action

The canonical finite point type is `IsotropicPoint`.  This file derives its
`Fin 63` enumeration and transports the native automorphism action to an
actual permutation representation.  It deliberately makes no claim about
the 189 incident flags or about a quotient stabilizer.
-/

namespace InfoGeometry.Algebra.Zorn.G2ImaginaryPointPermutation

open InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def pointEnum : Fin 63 ≃ IsotropicPoint :=
  (Fintype.equivFinOfCardEq point_card).symm

noncomputable def pointPerm (g : SplitOctF2Aut) : Equiv.Perm (Fin 63) :=
  pointEnum.trans ((MulAction.toPerm g).trans pointEnum.symm)

theorem pointPerm_intertwines (g : SplitOctF2Aut) (i : Fin 63) :
    pointEnum (pointPerm g i) = g • pointEnum i := by
  simp [pointPerm, MulAction.toPerm]

theorem pointPerm_mul (g h : SplitOctF2Aut) :
    pointPerm (g * h) = pointPerm g * pointPerm h := by
  ext i
  apply pointEnum.injective
  rw [pointPerm_intertwines, pointPerm_intertwines, pointPerm_intertwines,
    mul_smul]

end InfoGeometry.Algebra.Zorn.G2ImaginaryPointPermutation
