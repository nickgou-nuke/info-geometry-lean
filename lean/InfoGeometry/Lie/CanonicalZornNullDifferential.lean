import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Lie.CanonicalZornDiracKahler

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornNullDifferential

open InfoGeometry.Lie.CanonicalZornCircularHodgeTransport
open InfoGeometry.Lie.CanonicalZornClifford
open InfoGeometry.Lie.CanonicalZornDiracKahler

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- The algebraic null differential d = ⋆ + K on the native Zorn carrier. -/
def dNull : EndCZ :=
  cl11Rep (e0 + e1)

/-- dNull is nilpotent: d² = 0.
    Proved purely from the split signature Q(1, 1) = 1² - 1² = 0. -/
theorem dNull_sq : dNull * dNull = 0 := by
  dsimp [dNull, e0, e1]
  rw [← map_mul]
  have h_pair : ((1 : ℝ), (0 : ℝ)) + (0, 1) = (1, 1) := by ext <;> simp
  have h_clifford :
      (CliffordAlgebra.ι Q11 (1, 0) + CliffordAlgebra.ι Q11 (0, 1) : CliffordAlgebra Q11) =
      CliffordAlgebra.ι Q11 (1, 1) := by
    rw [← map_add, h_pair]
  rw [h_clifford, CliffordAlgebra.ι_sq_scalar, Q11_apply]
  norm_num

/-- dNull anticommutes with graded chirality: {d, ω} = 0. -/
theorem dNull_anticommute_omega :
    dNull * cl11Rep omega = -(cl11Rep omega * dNull) := by
  dsimp [dNull]
  rw [map_add, add_mul, mul_add]
  have h0 := cl11Rep_e0_anticommute_omega
  have h1 := cl11Rep_e1_anticommute_omega
  rw [h0, h1, neg_add]

/-- The Dirac-Kähler operator for the null differential evaluates to 2 • ⋆. -/
theorem diracKahler_dNull_eq :
    diracKahler dNull = (2 : ℝ) • circularHodgeStar := by
  dsimp [diracKahler, codiff, dNull]
  have h_star := cl11Rep_e0
  rw [map_add, h_star]
  have h_anti : circularHodgeStar * cl11Rep e1 = -(cl11Rep e1 * circularHodgeStar) := by
    rw [cl11Rep_e1]
    have h1 : circularHodgeStar * (circularHodgeStar * circularGradedChirality) =
        circularGradedChirality := by
      rw [← mul_assoc, circularHodgeStar_sq, one_mul]
    have h2 : (circularHodgeStar * circularGradedChirality) * circularHodgeStar =
        -circularGradedChirality := by
      have h_comm : circularGradedChirality * circularHodgeStar =
          -(circularHodgeStar * circularGradedChirality) := by
        rw [← neg_neg (circularGradedChirality * circularHodgeStar),
            ← circularHodgeStar_gradedChirality_anticommutes]
      rw [mul_assoc, h_comm, mul_neg, ← mul_assoc, circularHodgeStar_sq, one_mul]
    rw [h1, h2, neg_neg]
  have h_conj :
      circularHodgeStar * (circularHodgeStar + cl11Rep e1) * circularHodgeStar =
        circularHodgeStar - cl11Rep e1 := by
    simp only [mul_add, add_mul, circularHodgeStar_sq, one_mul]
    rw [h_anti, neg_mul, mul_assoc, circularHodgeStar_sq, mul_one, sub_eq_add_neg]
  rw [h_conj]
  simp only [sub_neg_eq_add]
  rw [two_smul]
  abel

/-- The Hodge Laplacian for the null differential is the constant mass gap 4 • id. -/
theorem hodgeLaplacian_dNull_eq :
    hodgeLaplacian dNull = (4 : ℝ) • (1 : EndCZ) := by
  rw [← diracKahler_sq dNull dNull_sq, diracKahler_dNull_eq]
  rw [smul_mul_smul, circularHodgeStar_sq]
  norm_num

end InfoGeometry.Lie.CanonicalZornNullDifferential
