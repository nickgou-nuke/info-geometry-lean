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

namespace InfoGeometry.Clifford.Hurwitz3DGeometricAlgebra

open scoped TensorProduct
open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Algebra.Zorn

theorem cl11_pseudoscalar_sq :
    InfoGeometry.Clifford.Hestenes.Pseudoscalar *
      InfoGeometry.Clifford.Hestenes.Pseudoscalar = 1 := by
  simpa using InfoGeometry.Clifford.Hestenes.pseudoscalar_sq

noncomputable def cl11_equiv_mat2 :
    InfoGeometry.Clifford.Cl11Quaternion.Cl11 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  InfoGeometry.Clifford.Cl11Quaternion.cliffordEquivMat

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
    (X Y : InfoGeometry.Canonical.ZornMatrix ℝ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        concreteCrossProduct3
        (mulZ X Y)
      =
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        concreteCrossProduct3 X *
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        concreteCrossProduct3 Y := by
  simpa using InfoGeometry.Algebra.Zorn.detZ_mul X Y

noncomputable def cl44_complexification_equiv :
    InfoGeometry.Clifford.SplitCl44Complexification.Cl44Complex ≃ₐ[ℂ]
      ℂ ⊗[ℝ] InfoGeometry.Clifford.BottPeriodicity.Cl44 :=
  InfoGeometry.Clifford.SplitCl44Complexification.cl44ComplexificationEquiv

end InfoGeometry.Clifford.Hurwitz3DGeometricAlgebra
