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

end InfoGeometry.Lie.CanonicalZornNullDifferential
