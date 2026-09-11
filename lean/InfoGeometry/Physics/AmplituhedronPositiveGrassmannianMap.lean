import InfoGeometry.Physics.AmplituhedronPenroseTransform
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics.AmplituhedronPositiveGrassmannianMap

open Amplituhedron

variable (k n m : ℕ)

/-- A momentum twistor packet with entrywise nonnegative coordinates. -/
abbrev PositiveMomentumTwistors :=
  {Z : MomentumTwistors k n m // ∀ i j, 0 ≤ Z.Z_matrix i j}

theorem is_positive (Z : PositiveMomentumTwistors k n m) :
    ∀ i j, 0 ≤ Z.1.Z_matrix i j := Z.2

/-- The amplituhedron map `Φ_Z(C) = C * Z` at the level of matrices. -/
def PhiZ (C : PositiveGrassmannian k n) (Z : PositiveMomentumTwistors k n m) :
    Matrix (Fin k) (Fin (k + m)) ℝ :=
  Amplituhedron.amplituhedron_space (k := k) (n := n) (m := m) C Z.1

/-- Entrywise nonnegativity of the amplituhedron map from nonnegative input packets. -/
theorem PhiZ_entrywise_nonnegative
  (C : PositiveGrassmannian k n) (Z : PositiveMomentumTwistors k n m) :
    ∀ i j, 0 ≤ PhiZ k n m C Z i j := by
  intro i j
  dsimp [PhiZ, Amplituhedron.amplituhedron_space]
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (C.2 i t) (Z.2 t j)

theorem PhiZ_entrywise_positive
    (hn : 0 < n) (C : PositiveGrassmannian k n)
    (Z : PositiveMomentumTwistors k n m)
    (hC : ∀ i j, 0 < C.C_matrix i j)
    (hZ : ∀ i j, 0 < Z.1.Z_matrix i j) :
    ∀ i j, 0 < PhiZ k n m C Z i j := by
  exact Amplituhedron.matrix_mul_entrywise_positive k n m hn C.C_matrix Z.1.Z_matrix hC hZ

/-- The amplituhedron map is computed by matrix multiplication. -/
theorem PhiZ_eq_amplituhedron_space
    (C : PositiveGrassmannian k n) (Z : PositiveMomentumTwistors k n m) :
    PhiZ k n m C Z = Amplituhedron.amplituhedron_space (k := k) (n := n) (m := m) C Z.1 := by
  rfl

end InfoGeometry.Physics.AmplituhedronPositiveGrassmannianMap
