import Mathlib
import InfoGeometry.Canonical.H3ZornJordanTripleBridge
import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceZeroJordanTripleRestriction

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev H3 := H3Zorn ℝ

private theorem peirceZero_add
    {x y : H3} (hx : InPeirceZero x) (hy : InPeirceZero y) :
    InPeirceZero (x + y) := by
  rcases hx with ⟨hx₁, hxa, hxc⟩
  rcases hy with ⟨hy₁, hya, hyc⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [H3Zorn.add_readback, hx₁, hy₁]
  · simpa [H3Zorn.add_readback, ZornVectorMatrix.zero, ZornVectorMatrix.add, hxa, hya]
  · simpa [H3Zorn.add_readback, ZornVectorMatrix.zero, ZornVectorMatrix.add, hxc, hyc]

/-! The fixed `e₁` Peirce-zero sector is a Jordan triple subspace.  This is
the exact restriction needed before any Kantor/TKK construction; it does not
assert either Kantor identity. -/

theorem candidateJordanTriple_preserves_peirceZero
    {x y z : H3} (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) := by
  have hxy : InPeirceZero (x * y) := by
    simpa only [candidateJordanMul_eq_mul] using
      candidateJordanMul_preserves_peirceZero hx hy
  have hzy : InPeirceZero (z * y) := by
    simpa only [candidateJordanMul_eq_mul] using
      candidateJordanMul_preserves_peirceZero hz hy
  have hxy_z : InPeirceZero ((x * y) * z) := by
    simpa only [candidateJordanMul_eq_mul] using
      candidateJordanMul_preserves_peirceZero hxy hz
  have hzy_x : InPeirceZero ((z * y) * x) := by
    simpa only [candidateJordanMul_eq_mul] using
      candidateJordanMul_preserves_peirceZero hzy hx
  have hxz : InPeirceZero (x * z) := by
    simpa only [candidateJordanMul_eq_mul] using
      candidateJordanMul_preserves_peirceZero hx hz
  have hxz_y : InPeirceZero ((x * z) * y) := by
    simpa only [candidateJordanMul_eq_mul] using
      candidateJordanMul_preserves_peirceZero hxz hy
  rcases hxy_z with ⟨h₁, h₂, h₃⟩
  rcases hzy_x with ⟨k₁, k₂, k₃⟩
  rcases hxz_y with ⟨l₁, l₂, l₃⟩
  have hsum : InPeirceZero (((x * y) * z) + ((z * y) * x)) := by
    apply peirceZero_add
    · exact ⟨h₁, h₂, h₃⟩
    · exact ⟨k₁, k₂, k₃⟩
  exact sub_preserves_peirceZero hsum ⟨l₁, l₂, l₃⟩

theorem peirceZero_triple_closure
    (x y z : H3) (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) :=
  candidateJordanTriple_preserves_peirceZero hx hy hz

end InfoGeometry.Canonical.SplitAlbertPeirceZeroJordanTripleRestriction
