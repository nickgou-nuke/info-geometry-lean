import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.Cl11Quaternion
import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Clifford.SplitCl44Complexification
import InfoGeometry.Algebra.Zorn.ConcreteComposition
import InfoGeometry.Canonical.AlbertCayleyDickson

/-!
# Hurwitz algebras from geometric-algebra pieces

This file records the theorem-backed algebraic statements that the repository
already owns for the Hurwitz/split-Hurwitz corridor.
-/

namespace Hurwitz3DGeometricAlgebra

open scoped TensorProduct
open AlbertCayleyDickson
open ConcreteComposition

theorem cl11_pseudoscalar_sq :
    Hestenes.Pseudoscalar * Hestenes.Pseudoscalar = 1 := by
  simpa using Hestenes.pseudoscalar_sq

noncomputable def cl11_equiv_mat2 :
    Cl11Quaternion.Cl11 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  Cl11Quaternion.cliffordEquivMat

theorem splitOctonion_has_nonzero_zero_divisors :
    ∃ x y : SplitOctonion ℝ,
      x ≠ 0 ∧ y ≠ 0 ∧
        AlbertStep.mul x y = 0 := by
  simpa [SplitOctonion, SplitQuaternion]
    using
      (AlbertStep.gamma_one_has_canonical_zero_divisors
          (F := ℝ)
          (A := SplitQuaternion ℝ))

theorem zorn_det_mul
    (X Y : ZornCell ℝ) :
    ZornCell.detZ (X * Y) = ZornCell.detZ X * ZornCell.detZ Y := by
  simpa using
    ZornCell.detZ_mul X Y

noncomputable def cl44_complexification_equiv :
    SplitCl44Complexification.Cl44Complex ≃ₐ[ℂ]
      ℂ ⊗[ℝ] InfoGeometry.Clifford.BottPeriodicity.Cl44 :=
  SplitCl44Complexification.cl44ComplexificationEquiv

end Hurwitz3DGeometricAlgebra
