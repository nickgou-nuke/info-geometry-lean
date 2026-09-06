import InfoGeometry.Clifford.KoszulFoundation
import Mathlib.Tactic

/-!
# Four-frame volume signs and dimension-independent paravector norm

This is a specialization of the existing native Clifford volume-square
calculation, not another gamma representation. Orthogonality and normalized
vector squares are the specified frame data. In four dimensions the six
Koszul exchanges contribute +1, so the volume square is the product of the
four vector squares. Euclidean (4,0) and split (2,2) frames give +1.

The paravector identity is a Clifford product. It is not a determinant of a
matrix with multivector entries, and no Hodge operator is silently selected.
-/

noncomputable section

namespace InfoGeometry.Clifford.FourFrameVolumeAndParavector

open InfoGeometry.Clifford.KoszulFoundation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The exact four-frame case of the existing Koszul square theorem. -/
theorem volume_four_square (Q : QuadraticForm ℝ V) (a b c d : V)
    (ho : [a, b, c, d].Pairwise (fun v w => Q.IsOrtho v w)) :
    cliffordVolumeElement Q [a, b, c, d] * cliffordVolumeElement Q [a, b, c, d] =
      algebraMap ℝ (CliffordAlgebra Q) (Q a * Q b * Q c * Q d) := by
  rw [cliffordVolumeElement_sq_of_pairwise _ ho]
  congr 1
  simp [cliffordVolumeSquareScalar] <;> ring

theorem volume_four_euclidean_square (Q : QuadraticForm ℝ V) (a b c d : V)
    (ho : [a, b, c, d].Pairwise (fun v w => Q.IsOrtho v w))
    (ha : Q a = 1) (hb : Q b = 1) (hc : Q c = 1) (hd : Q d = 1) :
    cliffordVolumeElement Q [a, b, c, d] * cliffordVolumeElement Q [a, b, c, d] = 1 := by
  rw [volume_four_square Q a b c d ho, ha, hb, hc, hd]
  simp

theorem volume_four_split22_square (Q : QuadraticForm ℝ V) (a b c d : V)
    (ho : [a, b, c, d].Pairwise (fun v w => Q.IsOrtho v w))
    (ha : Q a = 1) (hb : Q b = 1) (hc : Q c = -1) (hd : Q d = -1) :
    cliffordVolumeElement Q [a, b, c, d] * cliffordVolumeElement Q [a, b, c, d] = 1 := by
  rw [volume_four_square Q a b c d ho, ha, hb, hc, hd]
  simp

theorem volume_four_lorentz13_square (Q : QuadraticForm ℝ V) (a b c d : V)
    (ho : [a, b, c, d].Pairwise (fun v w => Q.IsOrtho v w))
    (ha : Q a = 1) (hb : Q b = -1) (hc : Q c = -1) (hd : Q d = -1) :
    cliffordVolumeElement Q [a, b, c, d] * cliffordVolumeElement Q [a, b, c, d] = -1 := by
  rw [volume_four_square Q a b c d ho, ha, hb, hc, hd]
  simp

/-- Scalar-plus-vector norm in arbitrary dimension and signature. -/
theorem paravector_mul_conjugate (Q : QuadraticForm ℝ V) (t : ℝ) (v : V) :
    (algebraMap ℝ (CliffordAlgebra Q) t + CliffordAlgebra.ι Q v) *
        (algebraMap ℝ (CliffordAlgebra Q) t - CliffordAlgebra.ι Q v) =
      algebraMap ℝ (CliffordAlgebra Q) (t ^ 2 - Q v) := by
  have hcomm := (Algebra.commutes t (CliffordAlgebra.ι Q v)).eq
  calc
    (algebraMap ℝ (CliffordAlgebra Q) t + CliffordAlgebra.ι Q v) *
          (algebraMap ℝ (CliffordAlgebra Q) t - CliffordAlgebra.ι Q v) =
        algebraMap ℝ (CliffordAlgebra Q) t * algebraMap ℝ (CliffordAlgebra Q) t -
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v := by
      noncomm_ring [hcomm]
    _ = algebraMap ℝ (CliffordAlgebra Q) (t ^ 2 - Q v) := by
      rw [CliffordAlgebra.ι_sq_scalar, ← map_mul, ← map_sub, pow_two]

/-- Exterior-degree duality sends a bivector to degree `D-2`; having vector
degree in this Hodge construction is the three-dimensional case. -/
theorem hodge_bivector_degree_is_one_iff (D : ℕ) (hD : 2 ≤ D) :
    D - 2 = 1 ↔ D = 3 := by omega

/-- Hodge duality reverses parity in odd dimension, and preserves it in even
dimension. In dimension four it is not a parity-exchanging map. -/
theorem hodge_degree_parity_even_dimension (D k : ℕ) (hk : k ≤ D)
    (hD : D % 2 = 0) : (D - k) % 2 = k % 2 := by omega

end InfoGeometry.Clifford.FourFrameVolumeAndParavector
