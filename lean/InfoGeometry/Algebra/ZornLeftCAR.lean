import InfoGeometry.Algebra.ZornPinorReconstruction
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Genuine associative CAR operators on the eight-dimensional Zorn module

Zorn multiplication is not operator composition. Left alternativity supplies
exactly the square identity needed for a native Clifford lift into `Module.End`.
The resulting representation has quadratic form `|v|² - |u|²` on `V × V`.
No faithfulness, Pin-group identification, or Hilbert-space adjoint is assumed.
-/

namespace InfoGeometry.Algebra.ZornLeftCAR

open InfoGeometry.Algebra
open ZornPinorReconstruction

noncomputable section

/-- Bilinear multiplication, curried into native linear endomorphisms. -/
def leftMultiplication : Z →ₗ[ℝ] Module.End ℝ Z where
  toFun X :=
    { toFun := ZornVectorMatrix.mul X
      map_add' Y W := ZornVectorMatrix.mul_add X Y W
      map_smul' r Y := ZornVectorMatrix.mul_smul r X Y }
  map_add' X Y := by
    apply LinearMap.ext
    intro W
    change ZornVectorMatrix.mul (ZornVectorMatrix.add X Y) W =
      ZornVectorMatrix.add (ZornVectorMatrix.mul X W) (ZornVectorMatrix.mul Y W)
    exact ZornVectorMatrix.add_mul X Y W
  map_smul' r X := by
    apply LinearMap.ext
    intro W
    change ZornVectorMatrix.mul (ZornVectorMatrix.smul r X) W =
      ZornVectorMatrix.smul r (ZornVectorMatrix.mul X W)
    exact ZornVectorMatrix.smul_mul r X W

@[simp] theorem leftMultiplication_apply (X Y : Z) :
    leftMultiplication X Y = ZornVectorMatrix.mul X Y := rfl

@[simp] theorem leftMultiplication_one :
    leftMultiplication ZornVectorMatrix.one = 1 := by
  apply LinearMap.ext
  intro X
  change ZornVectorMatrix.mul ZornVectorMatrix.one X = X
  exact ZornVectorMatrix.one_mul X

theorem leftMultiplication_injective : Function.Injective leftMultiplication := by
  intro X Y h
  have h1 := LinearMap.congr_fun h ZornVectorMatrix.one
  simpa only [leftMultiplication_apply, ZornVectorMatrix.mul_one] using h1

/-- This is alternativity, not an illicit associativity rewrite. -/
theorem leftMultiplication_square (X : Z) :
    leftMultiplication X * leftMultiplication X =
      leftMultiplication (ZornVectorMatrix.mul X X) := by
  apply LinearMap.ext
  intro Y
  change ZornVectorMatrix.mul X (ZornVectorMatrix.mul X Y) =
    ZornVectorMatrix.mul (ZornVectorMatrix.mul X X) Y
  have h := ZornVectorMatrix.associator_left_alternative X Y
  have hs : ZornVectorMatrix.mul (ZornVectorMatrix.mul X X) Y -
      ZornVectorMatrix.mul X (ZornVectorMatrix.mul X Y) = 0 := h
  exact (sub_eq_zero.mp hs).symm

/-- Polarization of the native left-alternativity identity. -/
theorem leftMultiplication_anticommutator (X Y : Z) :
    leftMultiplication X * leftMultiplication Y +
        leftMultiplication Y * leftMultiplication X =
      leftMultiplication (ZornVectorMatrix.mul X Y + ZornVectorMatrix.mul Y X) := by
  have hm : ZornVectorMatrix.mul (X + Y) (X + Y) =
      ZornVectorMatrix.mul X X + ZornVectorMatrix.mul X Y +
        (ZornVectorMatrix.mul Y X + ZornVectorMatrix.mul Y Y) := by
    change ZornVectorMatrix.mul (ZornVectorMatrix.add X Y)
        (ZornVectorMatrix.add X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.add (ZornVectorMatrix.mul X X)
          (ZornVectorMatrix.mul X Y))
        (ZornVectorMatrix.add (ZornVectorMatrix.mul Y X)
          (ZornVectorMatrix.mul Y Y))
    rw [ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
      ZornVectorMatrix.mul_add]
  have h := leftMultiplication_square (X + Y)
  rw [hm] at h
  simp only [map_add, add_mul, mul_add, leftMultiplication_square] at h
  have hc := congrArg (fun T : Module.End ℝ Z =>
      T - leftMultiplication (ZornVectorMatrix.mul X X) -
        leftMultiplication (ZornVectorMatrix.mul Y Y)) h
  rw [map_add]
  convert hc using 1 <;> abel

/-- An explicit obstruction to treating the left action as an algebra homomorphism. -/
theorem leftMultiplication_not_multiplicative :
    leftMultiplication (ZornVectorMatrix.U 0) * leftMultiplication (ZornVectorMatrix.U 1) ≠
      leftMultiplication (ZornVectorMatrix.mul (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1)) := by
  intro h
  have h2 := LinearMap.congr_fun h (ZornVectorMatrix.U 2)
  change ZornVectorMatrix.mul (ZornVectorMatrix.U 0)
      (ZornVectorMatrix.mul (ZornVectorMatrix.U 1) (ZornVectorMatrix.U 2)) =
    ZornVectorMatrix.mul
      (ZornVectorMatrix.mul (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1))
      (ZornVectorMatrix.U 2) at h2
  norm_num [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot,
    ZornVec3.cross, ZornVec3.basis, Fin.sum_univ_three] at h2
  norm_num [Fin.ext_iff] at h2
 /-- A quaternion identity between elements does not extend to their full-module left actions. -/
theorem gamma_operator_product_ne :
    leftMultiplication (gamma (ZornVec3.basis 0)) *
        leftMultiplication (gamma (ZornVec3.basis 1)) ≠
      leftMultiplication (gamma (ZornVec3.basis 2)) := by
  intro h
  have h1 := LinearMap.congr_fun h polePlus
  have h2 := congrArg (fun X : Z => X.v 2) h1
  norm_num [Module.End.mul_apply, leftMultiplication_apply, gamma, polePlus,
    ZornVectorMatrix.E11, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
    ZornVec3.dot, ZornVec3.cross, ZornVec3.basis, Fin.sum_univ_three] at h2
  norm_num [Fin.ext_iff] at h2
def raise (u : V) : Module.End ℝ Z := leftMultiplication (creation u)
def lower (u : V) : Module.End ℝ Z := leftMultiplication (annihilation u)

theorem raise_square (u : V) : raise u * raise u = 0 := by
  simp only [raise, leftMultiplication_square, creation_square, map_zero]

theorem lower_square (u : V) : lower u * lower u = 0 := by
  simp only [lower, leftMultiplication_square, annihilation_square, map_zero]

theorem raise_raise_car (u v : V) : raise u * raise v + raise v * raise u = 0 := by
  simp only [raise, leftMultiplication_anticommutator, creation_anticommutator, map_zero]

theorem lower_lower_car (u v : V) : lower u * lower v + lower v * lower u = 0 := by
  simp only [lower, leftMultiplication_anticommutator, annihilation_anticommutator, map_zero]

/-- Genuine CAR: multiplication here is associative composition in `Module.End`. -/
theorem raise_lower_car (u v : V) :
    raise u * lower v + lower v * raise u = ZornVec3.dot u v • (1 : Module.End ℝ Z) := by
  simp only [raise, lower, leftMultiplication_anticommutator, element_car,
    map_smul, leftMultiplication_one]

/-- Native bilinear form with three negative and three positive coordinates. -/
def splitBilin : LinearMap.BilinForm ℝ (V × V) where
  toFun p :=
    { toFun q := ZornVec3.dot p.2 q.2 - ZornVec3.dot p.1 q.1
      map_add' q r := by
        change ZornVec3.dot p.2 (q.2 + r.2) - ZornVec3.dot p.1 (q.1 + r.1) = _
        rw [ZornVec3.dot_add_right, ZornVec3.dot_add_right]
        ring
      map_smul' c q := by
        change ZornVec3.dot p.2 (c • q.2) - ZornVec3.dot p.1 (c • q.1) =
          c * (ZornVec3.dot p.2 q.2 - ZornVec3.dot p.1 q.1)
        rw [ZornVec3.dot_smul_right, ZornVec3.dot_smul_right]
        ring }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    change ZornVec3.dot (p.2 + q.2) r.2 - ZornVec3.dot (p.1 + q.1) r.1 = _
    rw [ZornVec3.dot_add_left, ZornVec3.dot_add_left]
    change _ = (ZornVec3.dot p.2 r.2 - ZornVec3.dot p.1 r.1) +
      (ZornVec3.dot q.2 r.2 - ZornVec3.dot q.1 r.1)
    ring
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    change ZornVec3.dot (c • p.2) q.2 - ZornVec3.dot (c • p.1) q.1 =
      c * (ZornVec3.dot p.2 q.2 - ZornVec3.dot p.1 q.1)
    rw [ZornVec3.dot_smul_left, ZornVec3.dot_smul_left]
    ring

def splitQuadratic : QuadraticForm ℝ (V × V) := splitBilin.toQuadraticMap

@[simp] theorem splitQuadratic_apply (p : V × V) :
    splitQuadratic p = ZornVec3.dot p.2 p.2 - ZornVec3.dot p.1 p.1 := rfl

/-- The six vector directions in the existing Zorn carrier. -/
def cliffordVector : (V × V) →ₗ[ℝ] Z where
  toFun p := ZornVectorMatrix.offDiagonal (-(p.1 + p.2)) (p.1 - p.2)
  map_add' p q := by
    ext i <;> simp [ZornVectorMatrix.offDiagonal, ZornVectorMatrix.add] <;> ring
  map_smul' c p := by
    ext i <;> simp [ZornVectorMatrix.offDiagonal, ZornVectorMatrix.smul] <;> ring

theorem cliffordVector_square (p : V × V) :
    ZornVectorMatrix.mul (cliffordVector p) (cliffordVector p) =
      splitQuadratic p • ZornVectorMatrix.one := by
  ext i <;> (try fin_cases i) <;>
    simp [cliffordVector, splitQuadratic_apply, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.mul, ZornVectorMatrix.smul, ZornVectorMatrix.one,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

def cliffordGenerator : (V × V) →ₗ[ℝ] Module.End ℝ Z :=
  leftMultiplication.comp cliffordVector

theorem cliffordGenerator_square (p : V × V) :
    cliffordGenerator p * cliffordGenerator p =
      splitQuadratic p • (1 : Module.End ℝ Z) := by
  change leftMultiplication (cliffordVector p) * leftMultiplication (cliffordVector p) = _
  rw [leftMultiplication_square, cliffordVector_square, map_smul, leftMultiplication_one]

/-- The universal property is used only with the associative endomorphism target. -/
def cliffordRepresentation : CliffordAlgebra splitQuadratic →ₐ[ℝ] Module.End ℝ Z :=
  CliffordAlgebra.lift splitQuadratic
    ⟨cliffordGenerator, fun p => by
      simpa only [Algebra.algebraMap_eq_smul_one] using cliffordGenerator_square p⟩

@[simp] theorem cliffordRepresentation_iota (p : V × V) :
    cliffordRepresentation (CliffordAlgebra.ι splitQuadratic p) = cliffordGenerator p := by
  exact CliffordAlgebra.lift_ι_apply _ _ _

theorem cliffordVector_negative (u : V) : cliffordVector (u, 0) = gamma u := by
  ext i <;> simp [cliffordVector, gamma, ZornVectorMatrix.offDiagonal]

theorem cliffordVector_positive (u : V) : cliffordVector (0, u) = kappa u := by
  ext i <;> simp [cliffordVector, kappa, ZornVectorMatrix.offDiagonal]

end
end InfoGeometry.Algebra.ZornLeftCAR
