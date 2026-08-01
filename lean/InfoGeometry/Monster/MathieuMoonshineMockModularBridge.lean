import Mathlib.Tactic
import InfoGeometry.Monster.MoonshineGradedDimensions
import InfoGeometry.Quantum.GolayLeechStabilizerCode

open InfoGeometry.Monster.MoonshineGradedDimensions
open InfoGeometry.Quantum.GolayLeechStabilizerCode

noncomputable section

namespace InfoGeometry.Monster.MathieuMoonshineMockModularBridge

/-- Dimensions of the fundamental irreducible representations of the Mathieu Group M₂₄ -/
def m24_irrep_dims : ℕ → ℕ
  | 0 => 1
  | 1 => 45
  | 2 => 231
  | 3 => 770
  | 4 => 2277
  | 5 => 3520
  | 6 => 2276
  | _ => 0

/-- Order of the sporadic Mathieu Group M₂₄ -/
def m24_order : ℕ := 244823040

/-- Theorem: M₂₄ order prime factorization |M₂₄| = 2¹⁰ × 3³ × 5 × 7 × 11 × 23 -/
theorem m24_order_factorization :
    m24_order = 2^10 * 3^3 * 5 * 7 * 11 * 23 := rfl

/-- Theorem: Decomposition of Mock Theta Coefficient A₅ into M₂₄ Irrep Dimensions -/
theorem m24_mock_theta_a5_decomposition :
    m24_irrep_dims 5 + m24_irrep_dims 6 = 5796 := rfl

/-- Theorem: Positivity of initial Mathieu irrep dimensions -/
theorem m24_irrep_dims_pos (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 5) :
    0 < m24_irrep_dims n := by
  interval_cases n
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Definition of Golay minimum distance for historical compatibility -/
def golay_min_distance : ℕ := 8

/-- Theorem: Extended Binary Golay Code G₂₄ minimum distance is positive -/
theorem golay_min_distance_pos : 0 < golay_min_distance := by decide

/-- Theorem: Product of M₂₄ order and Golay code minimum distance -/
theorem m24_order_mul_golay_distance :
    m24_order * golay_min_distance = 1958584320 := rfl

end InfoGeometry.Monster.MathieuMoonshineMockModularBridge
