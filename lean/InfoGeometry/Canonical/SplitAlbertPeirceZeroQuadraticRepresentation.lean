import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornQuadraticRepresentation
import InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ

/-- Membership in the fixed-`e1` Peirce-zero/transversal coordinate subspace.
This is exactly the lower-right Hermitian `2 x 2` split-octonion block. -/
def InPeirceZero (X : H3) : Prop :=
  X.α₁ = 0 ∧ X.a = 0 ∧ X.c = 0

@[simp] theorem peirceZeroEmbed_mem (p : PeirceZeroCoord) :
    InPeirceZero (peirceZeroEmbed p) := by
  simp [InPeirceZero, peirceZeroEmbed]

/-- Every element satisfying the coordinate predicate is reconstructed by the
native fixed-tripoten `peirceZeroEmbed`. -/
theorem eq_peirceZeroEmbed_of_mem
    {X : H3} (hX : InPeirceZero X) :
    X = peirceZeroEmbed ((X.α₂, X.α₃), X.b) := by
  rcases hX with ⟨h1, ha, hc⟩
  apply H3Zorn.ext_h3
  · simpa [peirceZeroEmbed] using h1
  · rfl
  · rfl
  · simpa [peirceZeroEmbed] using ha
  · rfl
  · simpa [peirceZeroEmbed] using hc

/-- The fixed-`e1` Peirce-zero space is closed under the installed Jordan
product.  This is the concrete lower-right `H2(O_s)` Jordan subalgebra fact. -/
theorem candidateJordanMul_preserves_peirceZero
    {X Y : H3} (hX : InPeirceZero X) (hY : InPeirceZero Y) :
    InPeirceZero (candidateJordanMul X Y) := by
  rw [eq_peirceZeroEmbed_of_mem hX, eq_peirceZeroEmbed_of_mem hY]
  rcases X with ⟨x1, x2, x3, xa, xb, xc⟩
  rcases Y with ⟨y1, y2, y3, ya, yb, yc⟩
  simp only [peirceZeroEmbed]
  rw [candidateJordanMul_trace_formula]
  simp [InPeirceZero, H3Zorn.linearTrace, H3Zorn.crossProduct,
    H3Zorn.adjointQuad, H3Zorn.add_readback, H3Zorn.sub_readback,
    H3Zorn.smul_readback, ZornVectorMatrix.zero, ZornVectorMatrix.add,
    ZornVectorMatrix.sub, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
    ZornVectorMatrix.norm, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.cross, H3Zorn.one,
    H3Zorn.one_readback,
    Fin.sum_univ_three] <;> ring_nf

/-- The Peirce-zero space is stable under real scalar multiplication. -/
theorem smul_preserves_peirceZero
    (r : ℝ) {X : H3} (hX : InPeirceZero X) :
    InPeirceZero (r • X) := by
  rcases hX with ⟨h1, ha, hc⟩
  simp only [H3Zorn.smul_readback]
  constructor
  · rw [h1]
    ring
  · constructor
    · rw [ha]
      exact ZornVectorMatrix.smul_zero r
    · rw [hc]
      exact ZornVectorMatrix.smul_zero r

/-- The Peirce-zero space is stable under subtraction. -/
theorem sub_preserves_peirceZero
    {X Y : H3} (hX : InPeirceZero X) (hY : InPeirceZero Y) :
    InPeirceZero (X - Y) := by
  rcases hX with ⟨hX1, hXa, hXc⟩
  rcases hY with ⟨hY1, hYa, hYc⟩
  have hzeroSub : ZornVectorMatrix.sub (0 : Zorn) 0 = 0 := by
    apply ZornVectorMatrix.ext
    all_goals simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  simp only [H3Zorn.sub_readback]
  constructor
  · rw [hX1, hY1]
    ring
  · constructor
    · rw [hXa, hYa]
      rw [hzeroSub]
    · rw [hXc, hYc]
      rw [hzeroSub]

/-- Quadratic Jordan representation written solely through the installed
Jordan product. -/
def quadraticJordanOp (y x : H3) : H3 :=
  (2 : ℝ) • candidateJordanMul y (candidateJordanMul y x) -
    candidateJordanMul (candidateJordanMul y y) x

/-- The polynomial Jordan formula is exactly the repository's native
McCrimmon/Freudenthal `U`-operator. -/
theorem quadraticJordanOp_eq_U (y x : H3) :
    quadraticJordanOp y x = U y x := by
  have h := H3ZornJordanQuadraticReconstruction y x
  simp only [quadraticJordanOp, candidateJordanMul, smul_sub, smul_smul,
    smul_add, T_smul_left, T_smul_right]
  calc
    _ = (1 / 2 : ℝ) • T y 1 (T y 1 x) -
        (1 / 4 : ℝ) • (T y 1 y).T 1 x := by
      congr 1 <;> norm_num
    _ = U y x := h.symm

/-- Main closure theorem: the quadratic Jordan representation preserves the
fixed-`e1` Peirce-zero/transversal subalgebra. -/
theorem quadraticJordanOp_preserves_peirceZero
    {y x : H3} (hy : InPeirceZero y) (hx : InPeirceZero x) :
    InPeirceZero (quadraticJordanOp y x) := by
  unfold quadraticJordanOp
  apply sub_preserves_peirceZero
  · apply smul_preserves_peirceZero
    exact candidateJordanMul_preserves_peirceZero hy
      (candidateJordanMul_preserves_peirceZero hy hx)
  · exact candidateJordanMul_preserves_peirceZero
      (candidateJordanMul_preserves_peirceZero hy hy) hx

/-- Hence the native `U`-operator preserves the Peirce-zero subalgebra. -/
theorem U_preserves_peirceZero
    {y x : H3} (hy : InPeirceZero y) (hx : InPeirceZero x) :
    InPeirceZero (U y x) := by
  rw [← quadraticJordanOp_eq_U]
  exact quadraticJordanOp_preserves_peirceZero hy hx

/-- The ten-dimensional transversal coordinate carrier from the previous owner. -/
abbrev SplitSpacetime10 := PeirceZeroCoord

/-- Projection from an ambient split-Albert element to the transversal
coordinates. -/
def fromH3 (X : H3) : SplitSpacetime10 :=
  ((X.α₂, X.α₃), X.b)

@[simp] theorem fromH3_peirceZeroEmbed (x : SplitSpacetime10) :
    fromH3 (peirceZeroEmbed x) = x := by
  rcases x with ⟨⟨d2, d3⟩, b⟩
  rfl

/-- Quadratic representation induced on the ten-dimensional split
`H2(O_s)` transversal. -/
def U10 (y x : SplitSpacetime10) : SplitSpacetime10 :=
  fromH3 (U (peirceZeroEmbed y) (peirceZeroEmbed x))

/-- The embedding strictly intertwines the induced 10D operator with the
ambient split-Albert `U`-operator. -/
theorem peirceZeroEmbed_U10 (y x : SplitSpacetime10) :
    peirceZeroEmbed (U10 y x) =
      U (peirceZeroEmbed y) (peirceZeroEmbed x) := by
  apply (eq_peirceZeroEmbed_of_mem
    (U_preserves_peirceZero (peirceZeroEmbed_mem y) (peirceZeroEmbed_mem x))).symm

/-- The native quadratic form on the ten-dimensional transversal is the split
`(5,5)` determinant already certified in the boundary owner. -/
def splitInterval10 (x : SplitSpacetime10) : ℝ :=
  h2SplitDet x.1.1 x.1.2 x.2

/-- Coordinate readout of the ten-dimensional interval as the diagonal
signature-`(5,5)` form. -/
theorem splitInterval10_eq_q55Real (x : SplitSpacetime10) :
    splitInterval10 x = q55Real (h2ToVec55 x.1.1 x.1.2 x.2) := by
  exact h2SplitDet_eq_q55Real x.1.1 x.1.2 x.2

end InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
