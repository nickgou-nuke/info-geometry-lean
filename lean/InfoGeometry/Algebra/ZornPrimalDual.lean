/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftInverse
import InfoGeometry.Algebra.ZornLeftDeterminant
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Primal and dual four-vectors in the native Zorn algebra

The two four-vectors are independent coordinates of one real eight-dimensional
split octonion. Their pairing is `(+---)`. This is not an identification of the
full split norm, of signature `(4,4)`, with a four-dimensional quadratic form.
The hyperplane is the kernel of a native linear functional. For a nonzero dual
vector it has dimension three; projective incidence additionally requires a
nonzero point and quotienting by nonzero scalar multiples.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornPrimalDual

open ZornLeftCAR
open ZornPinorReconstruction

/-- The upper chiral four-vector, on the existing Zorn carrier. -/
def primal : (Fin 4 → ℝ) →ₗ[ℝ] Z where
  toFun x := ⟨x 0, ![x 1, x 2, x 3], 0, 0⟩
  map_add' x y := by ext i <;> (try fin_cases i) <;> simp
  map_smul' c x := by ext i <;> (try fin_cases i) <;> simp

/-- The lower chiral four-vector, with the independent dual coordinates. -/
def dual : (Fin 4 → ℝ) →ₗ[ℝ] Z where
  toFun p := ⟨0, 0, ![p 1, p 2, p 3], p 0⟩
  map_add' x y := by ext i <;> (try fin_cases i) <;> simp
  map_smul' c x := by ext i <;> (try fin_cases i) <;> simp

/-- The two chiral coordinate spaces exhaust the eight-dimensional carrier. -/
def encode : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ≃ₗ[ℝ] Z where
  toFun xp := primal xp.1 + dual xp.2
  invFun z := (![z.a, z.v 0, z.v 1, z.v 2], ![z.b, z.w 0, z.w 1, z.w 2])
  left_inv xp := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [primal, dual, ZornVectorMatrix.add]
  right_inv z := by
    ext i <;> (try fin_cases i) <;> simp [primal, dual, ZornVectorMatrix.add]
  map_add' xp yq := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c xp := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]

/-- A dual four-vector determines the `(+---)` incidence functional. -/
def hyperplane (p : Fin 4 → ℝ) : Module.Dual ℝ (Fin 4 → ℝ) where
  toFun x := x 0 * p 0 - x 1 * p 1 - x 2 * p 2 - x 3 * p 3
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- A nonzero dual vector defines a genuine nonzero incidence functional. -/
theorem hyperplane_eq_zero_iff (p : Fin 4 → ℝ) : hyperplane p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h0 := LinearMap.congr_fun h ![1, 0, 0, 0]
    have h1 := LinearMap.congr_fun h ![0, 1, 0, 0]
    have h2 := LinearMap.congr_fun h ![0, 0, 1, 0]
    have h3 := LinearMap.congr_fun h ![0, 0, 0, 1]
    simp [hyperplane] at h0 h1 h2 h3
    ext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · rintro rfl
    ext x
    simp [hyperplane]

/-- The kernel of a nonzero dual four-vector has the expected dimension. -/
theorem hyperplane_ker_finrank (p : Fin 4 → ℝ) (hp : p ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (hyperplane p)) = 3 := by
  have hn : hyperplane p ≠ 0 := fun h => hp ((hyperplane_eq_zero_iff p).mp h)
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have hd : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
  rw [hd] at h
  omega

theorem norm_encode (x p : Fin 4 → ℝ) :
    ZornVectorMatrix.norm (encode (x, p)) = hyperplane p x := by
  simp [encode, primal, dual, ZornVectorMatrix.norm,
    ZornVec3.dot, Fin.sum_univ_three, hyperplane] <;> ring

theorem primal_square (x : Fin 4 → ℝ) :
    ZornVectorMatrix.mul (primal x) (primal x) = x 0 • primal x := by
  ext i <;> (try fin_cases i) <;>
    simp [primal, ZornVectorMatrix.mul, ZornVectorMatrix.smul,
      ZornVec3.dot, ZornVec3.cross] <;> ring

theorem dual_square (p : Fin 4 → ℝ) :
    ZornVectorMatrix.mul (dual p) (dual p) = p 0 • dual p := by
  ext i <;> (try fin_cases i) <;>
    simp [dual, ZornVectorMatrix.mul, ZornVectorMatrix.smul,
      ZornVec3.dot, ZornVec3.cross] <;> ring

theorem primal_operator_square (x : Fin 4 → ℝ) :
    leftMultiplication (primal x) * leftMultiplication (primal x) =
      x 0 • leftMultiplication (primal x) := by
  rw [leftMultiplication_square, primal_square, map_smul]

theorem dual_operator_square (p : Fin 4 → ℝ) :
    leftMultiplication (dual p) * leftMultiplication (dual p) =
      p 0 • leftMultiplication (dual p) := by
  rw [leftMultiplication_square, dual_square, map_smul]

/-- The full mixed anticommutator retains both time-coordinate terms. -/
theorem mixed_operator_anticommutator (x p : Fin 4 → ℝ) :
    leftMultiplication (primal x) * leftMultiplication (dual p) +
      leftMultiplication (dual p) * leftMultiplication (primal x) =
      p 0 • leftMultiplication (primal x) +
        x 0 • leftMultiplication (dual p) -
          hyperplane p x • (1 : Module.End ℝ Z) := by
  have h : ZornVectorMatrix.mul (primal x) (dual p) +
      ZornVectorMatrix.mul (dual p) (primal x) =
      p 0 • primal x + x 0 • dual p - hyperplane p x • ZornVectorMatrix.one := by
    rw [_root_.sub_eq_add_neg (p 0 • primal x + x 0 • dual p)
      (hyperplane p x • ZornVectorMatrix.one)]
    ext i <;> (try fin_cases i) <;>
      simp [primal, dual, hyperplane, ZornVectorMatrix.mul, ZornVectorMatrix.add,
        ZornVectorMatrix.smul, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;> ring
  rw [leftMultiplication_anticommutator, h, map_sub, map_add, map_smul,
    map_smul, map_smul, leftMultiplication_one]

/-- Incidence is exactly failure of invertibility of the genuine left action. -/
theorem incident_iff_not_isUnit (x p : Fin 4 → ℝ) :
    x ∈ LinearMap.ker (hyperplane p) ↔ ¬ IsUnit (leftMultiplication (encode (x, p))) := by
  simp only [LinearMap.mem_ker, leftMultiplication_isUnit_iff, norm_encode, not_not]

/-- The determinant of the represented left operator is the fourth power of
the primal/dual Minkowski pairing. -/
theorem leftMatrix_det_encode (x p : Fin 4 → ℝ) :
    (ZornLeftDeterminant.leftMatrix (encode (x, p))).det = (hyperplane p x) ^ 4 := by
  rw [ZornLeftDeterminant.leftMatrix_det, norm_encode]

/-- Incidence can equally be read from the determinant of the actual matrix. -/
theorem incident_iff_det_eq_zero (x p : Fin 4 → ℝ) :
    x ∈ LinearMap.ker (hyperplane p) ↔
      (ZornLeftDeterminant.leftMatrix (encode (x, p))).det = 0 := by
  rw [ZornLeftDeterminant.leftMatrix_det_eq_zero_iff, norm_encode]
  rfl

/-- On the diagonal section, the split norm restricts to the Minkowski square. -/
theorem norm_diagonal_section (x : Fin 4 → ℝ) :
    ZornVectorMatrix.norm (encode (x, x)) = x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by
  rw [norm_encode]
  change x 0 * x 0 - x 1 * x 1 - x 2 * x 2 - x 3 * x 3 = _
  ring

/-- Reversing the spatial dual coordinates gives a positive Euclidean section. -/
theorem norm_parity_section (x : Fin 4 → ℝ) :
    ZornVectorMatrix.norm (encode (x, ![x 0, -x 1, -x 2, -x 3])) =
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  rw [norm_encode]
  change x 0 * x 0 - x 1 * (-x 1) - x 2 * (-x 2) - x 3 * (-x 3) = _
  ring

end InfoGeometry.Algebra.ZornPrimalDual
