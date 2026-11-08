import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.IntegralZornAlternativeAlgebra

/-!
# Algebraic, coordinate-free Moufang identities for physical Zorn matrices

This file descends the coordinate-free Left, Right, and Middle Moufang identities
proven on `ZornVectorMatrix` down to the physical `Zorn` type using the injective
ring homomorphism `physicsToGenericZorn`. This avoids any deep coordinate unrolling
or tactic execution timeouts in Lean 4.
-/

noncomputable section

namespace InfoGeometry.Physics.SplitOctonionBraidSU3

open InfoGeometry.Canonical.IntegralZornAlternativeAlgebra
open InfoGeometry.Algebra.ZornVectorMatrix

/-- Left Moufang identity for physical Zorn matrices: z(x(zy)) = ((zx)z)y -/
theorem zorn_left_moufang_alg (X Y Z : Zorn) : 
    zornMul Z (zornMul X (zornMul Z Y)) = zornMul (zornMul (zornMul Z X) Z) Y := by
  apply physicsToGenericZorn_injective
  simp only [physicsToGenericZorn_mul]
  exact left_moufang _ _ _

/-- Right Moufang identity for physical Zorn matrices: ((yx)z)x = y(x(zx)) -/
theorem zorn_right_moufang_alg (X Y Z : Zorn) : 
    zornMul (zornMul (zornMul Y X) Z) X = zornMul Y (zornMul X (zornMul Z X)) := by
  apply physicsToGenericZorn_injective
  simp only [physicsToGenericZorn_mul]
  exact right_moufang _ _ _

/-- Middle Moufang identity for physical Zorn matrices: (xy)(zx) = x(yz)x -/
theorem zorn_middle_moufang_alg (X Y Z : Zorn) : 
    zornMul (zornMul X Y) (zornMul Z X) = zornMul X (zornMul (zornMul Y Z) X) := by
  apply physicsToGenericZorn_injective
  simp only [physicsToGenericZorn_mul]
  exact middle_moufang _ _ _

/-! ## Furey CAR Algebra -/

/-- Anticommutation relation {E_j, E_k} = 0 -/
theorem E_k_anticommute (j k : Fin 3) :
    zornAdd (zornMul (E_k j) (E_k k)) (zornMul (E_k k) (E_k j)) = zornZero := by
  apply zorn_ext
  · fin_cases j <;> fin_cases k <;> simp [zornMul, zornAdd, zornZero, E_k, e_k, dot3]
  · funext i
    fin_cases j <;> fin_cases k <;> fin_cases i <;>
      simp [zornMul, zornAdd, zornZero, E_k, e_k, cross3]
  · funext i
    fin_cases j <;> fin_cases k <;> fin_cases i <;>
      simp [zornMul, zornAdd, zornZero, E_k, e_k, cross3]
  · fin_cases j <;> fin_cases k <;> simp [zornMul, zornAdd, zornZero, E_k, e_k, dot3]

/-- Anticommutation relation {F_j, F_k} = 0 -/
theorem F_k_anticommute (j k : Fin 3) :
    zornAdd (zornMul (F_k j) (F_k k)) (zornMul (F_k k) (F_k j)) = zornZero := by
  apply zorn_ext
  · fin_cases j <;> fin_cases k <;> simp [zornMul, zornAdd, zornZero, F_k, e_k, dot3]
  · funext i
    fin_cases j <;> fin_cases k <;> fin_cases i <;>
      simp [zornMul, zornAdd, zornZero, F_k, e_k, cross3]
  · funext i
    fin_cases j <;> fin_cases k <;> fin_cases i <;>
      simp [zornMul, zornAdd, zornZero, F_k, e_k, cross3]
  · fin_cases j <;> fin_cases k <;> simp [zornMul, zornAdd, zornZero, F_k, e_k, dot3]

/-- Anticommutation relation {E_j, F_k} = \delta_jk * I -/
theorem E_F_anticommute (j k : Fin 3) :
    zornAdd (zornMul (E_k j) (F_k k)) (zornMul (F_k k) (E_k j)) =
      if j = k then I_zorn else zornZero := by
  apply zorn_ext
  · fin_cases j <;> fin_cases k <;>
      simp [zornMul, zornAdd, E_k, F_k, e_k, dot3, I_zorn, zornZero]
  · funext i
    fin_cases j <;> fin_cases k <;> fin_cases i <;>
      simp [zornMul, zornAdd, E_k, F_k, e_k, cross3, I_zorn, zornZero]
  · funext i
    fin_cases j <;> fin_cases k <;> fin_cases i <;>
      simp [zornMul, zornAdd, E_k, F_k, e_k, cross3, I_zorn, zornZero]
  · fin_cases j <;> fin_cases k <;>
      simp [zornMul, zornAdd, E_k, F_k, e_k, dot3, I_zorn, zornZero]

end InfoGeometry.Physics.SplitOctonionBraidSU3
