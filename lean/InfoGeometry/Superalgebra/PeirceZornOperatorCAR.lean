import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
import InfoGeometry.Algebra.ZornLeftCAR

/-!
# Operator CAR for the Peirce generators in the existing Zorn carrier

The Peirce products in `PeirceDeWittZornQuantization` are products in a
non-associative algebra. This file transports those generators to the existing
`ZornVectorMatrix` carrier, then uses its left action in `Module.End`, where
multiplication is associative composition. The result is an operator CAR
theorem for the Peirce generators, with the coefficient pairing preserved.
-/

namespace InfoGeometry.Superalgebra.PeirceZornOperatorCAR

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornPinorReconstruction
open InfoGeometry.Algebra.ZornLeftCAR
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-- The canonical Zorn-vector realization of a Peirce quark generator. -/
def quarkElementMap : ColorVec3 ℝ →ₗ[ℝ] ZornAlgebra ℝ where
  toFun := ZornAlgebra.quarkU
  map_add' u v := by
    change ZornAlgebra.quarkU (ColorVec3.add u v) =
      ZornAlgebra.add (ZornAlgebra.quarkU u) (ZornAlgebra.quarkU v)
    ext <;> simp [ZornAlgebra.quarkU, ZornAlgebra.add,
      ColorVec3.add, ColorVec3.zero]
  map_smul' c u := by
    change ZornAlgebra.quarkU (ColorVec3.smul c u) =
      ZornAlgebra.smul c (ZornAlgebra.quarkU u)
    ext <;> simp [ZornAlgebra.quarkU, ZornAlgebra.smul,
      ColorVec3.smul, ColorVec3.zero]

/-- The canonical Zorn-vector realization of a Peirce antiquark generator. -/
def antiquarkElementMap : ColorVec3 ℝ →ₗ[ℝ] ZornAlgebra ℝ where
  toFun := ZornAlgebra.antiquarkV
  map_add' u v := by
    change ZornAlgebra.antiquarkV (ColorVec3.add u v) =
      ZornAlgebra.add (ZornAlgebra.antiquarkV u) (ZornAlgebra.antiquarkV v)
    ext <;> simp [ZornAlgebra.antiquarkV, ZornAlgebra.add,
      ColorVec3.add, ColorVec3.zero]
  map_smul' c u := by
    change ZornAlgebra.antiquarkV (ColorVec3.smul c u) =
      ZornAlgebra.smul c (ZornAlgebra.antiquarkV u)
    ext <;> simp [ZornAlgebra.antiquarkV, ZornAlgebra.smul,
      ColorVec3.smul, ColorVec3.zero]

/-- The quark Peirce block acting by left multiplication on the Zorn module. -/
def quarkOperator : ColorVec3 ℝ →ₗ[ℝ]
    Module.End ℝ (ZornVectorMatrix ℝ) :=
  leftMultiplication.comp
    (ZornAlgebra.equivZornVectorMatrix.toLinearMap.comp quarkElementMap)

/-- The antiquark Peirce block acting by left multiplication on the Zorn module. -/
def antiquarkOperator : ColorVec3 ℝ →ₗ[ℝ]
    Module.End ℝ (ZornVectorMatrix ℝ) :=
  leftMultiplication.comp
    (ZornAlgebra.equivZornVectorMatrix.toLinearMap.comp antiquarkElementMap)

theorem equiv_quarkElementMap (u : ColorVec3 ℝ) :
    ZornAlgebra.equivZornVectorMatrix (quarkElementMap u) =
      creation (-ColorVec3.equivZornVec3 u) := by
  ext i <;> (try fin_cases i) <;>
    simp [quarkElementMap, ZornAlgebra.equivZornVectorMatrix,
      ZornAlgebra.toZornVectorMatrix, ColorVec3.equivZornVec3,
      ColorVec3.toZornVec3, ZornAlgebra.quarkU, creation,
      ZornVectorMatrix.offDiagonal]

theorem equiv_antiquarkElementMap (v : ColorVec3 ℝ) :
    ZornAlgebra.equivZornVectorMatrix (antiquarkElementMap v) =
      annihilation (-ColorVec3.equivZornVec3 v) := by
  ext i <;> (try fin_cases i) <;>
    simp [antiquarkElementMap, ZornAlgebra.equivZornVectorMatrix,
      ZornAlgebra.toZornVectorMatrix, ColorVec3.equivZornVec3,
      ColorVec3.toZornVec3, ZornAlgebra.antiquarkV, annihilation,
      ZornVectorMatrix.offDiagonal]

@[simp]
theorem quarkOperator_apply (u : ColorVec3 ℝ) :
    quarkOperator u = raise (-ColorVec3.equivZornVec3 u) := by
  change leftMultiplication
      (ZornAlgebra.equivZornVectorMatrix (quarkElementMap u)) = _
  rw [equiv_quarkElementMap]
  rfl

@[simp]
theorem antiquarkOperator_apply (v : ColorVec3 ℝ) :
    antiquarkOperator v = lower (-ColorVec3.equivZornVec3 v) := by
  change leftMultiplication
      (ZornAlgebra.equivZornVectorMatrix (antiquarkElementMap v)) = _
  rw [equiv_antiquarkElementMap]
  rfl

/-- The odd projector fixes the quark Peirce generator. -/
@[simp] theorem dewittOdd_quarkU (u : ColorVec3 ℝ) :
    ZornAlgebra.dewittOdd (ZornAlgebra.quarkU u) = ZornAlgebra.quarkU u := by
  rw [ZornAlgebra.dewittOdd_eq]
  rfl

/-- The odd projector fixes the antiquark Peirce generator. -/
@[simp] theorem dewittOdd_antiquarkV (v : ColorVec3 ℝ) :
    ZornAlgebra.dewittOdd (ZornAlgebra.antiquarkV v) = ZornAlgebra.antiquarkV v := by
  rw [ZornAlgebra.dewittOdd_eq]
  rfl

/--
The DeWitt odd subspace is not closed under the Zorn product: two distinct
quark basis generators have a nonzero odd cross-product component. Thus the
Peirce decomposition is not a `Z₂`-graded algebra in the usual multiplicative
sense, even though the separate even/odd component formulas hold.
-/
theorem quark_product_has_nonzero_odd_component :
    ZornAlgebra.dewittOdd
        (ZornAlgebra.mul
          (ZornAlgebra.quarkU (ColorVec3.e_r : ColorVec3 ℝ))
          (ZornAlgebra.quarkU ColorVec3.e_g)) ≠ ZornAlgebra.zero := by
  rw [ZornAlgebra.dewittOdd_eq, ZornAlgebra.supercolor_diquark_fusion]
  intro h
  have h₃ := congrArg (fun X : ZornAlgebra ℝ => X.v.c₃) h
  norm_num [ZornAlgebra.antiquarkV, ColorVec3.cross,
    ColorVec3.e_r, ColorVec3.e_g, ColorVec3.e_b,
    ZornAlgebra.zero, ColorVec3.zero] at h₃

/-- The quark operators anticommute under composition in `Module.End`. -/
theorem quarkOperator_anticommutator (u v : ColorVec3 ℝ) :
    quarkOperator u * quarkOperator v + quarkOperator v * quarkOperator u = 0 := by
  rw [quarkOperator_apply, quarkOperator_apply]
  exact raise_raise_car (-ColorVec3.equivZornVec3 u)
    (-ColorVec3.equivZornVec3 v)

/-- The antiquark operators anticommute under composition in `Module.End`. -/
theorem antiquarkOperator_anticommutator (u v : ColorVec3 ℝ) :
    antiquarkOperator u * antiquarkOperator v +
      antiquarkOperator v * antiquarkOperator u = 0 := by
  rw [antiquarkOperator_apply, antiquarkOperator_apply]
  exact lower_lower_car (-ColorVec3.equivZornVec3 u)
    (-ColorVec3.equivZornVec3 v)

/-- Mixed Peirce operators satisfy CAR in the associative endomorphism algebra. -/
theorem quark_antiquark_operator_CAR (u v : ColorVec3 ℝ) :
    quarkOperator u * antiquarkOperator v +
      antiquarkOperator v * quarkOperator u =
      ColorVec3.dot u v • (1 : Module.End ℝ (ZornVectorMatrix ℝ)) := by
  rw [quarkOperator_apply, antiquarkOperator_apply, raise_lower_car]
  rw [ZornVec3.dot_eq_sum_coords]
  simp [ColorVec3.equivZornVec3, ColorVec3.toZornVec3,
    ColorVec3.dot]

end InfoGeometry.Superalgebra.PeirceZornOperatorCAR
