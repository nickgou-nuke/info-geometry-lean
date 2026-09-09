import Mathlib
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ

/-- Coordinate predicate for the Peirce-zero sector at `e1 = diag(1,0,0)`.
This is exactly the lower-right Hermitian `2 x 2` split-octonion block. -/
def InPeirceZero (X : H3Zorn ℝ) : Prop :=
  X.α₁ = 0 ∧ X.a = 0 ∧ X.c = 0

@[simp] theorem peirceZeroEmbed_mem (p : PeirceZeroCoord) :
    InPeirceZero (peirceZeroEmbed p) := by
  simp [InPeirceZero, peirceZeroEmbed]

/-- Every coordinatewise Peirce-zero element is reconstructed by the native
`PeirceZeroCoord` embedding. -/
theorem peirceZeroEmbed_extract (X : H3Zorn ℝ) (hX : InPeirceZero X) :
    peirceZeroEmbed ((X.α₂, X.α₃), X.b) = X := by
  rcases hX with ⟨h1, ha, hc⟩
  apply H3Zorn.ext_h3 <;>
    simp [peirceZeroEmbed, h1, ha, hc]

/-- The repository's cubic `U`-operator is exactly the usual quadratic Jordan
representation

`U_y(x) = 2 y ∘ (y ∘ x) - y² ∘ x`

for the installed native Jordan multiplication on `H3Zorn ℝ`. -/
theorem U_eq_jordan_quadratic (y x : H3Zorn ℝ) :
    H3Zorn.U y x =
      (2 : ℝ) • (y * (y * x)) - (y * y) * x := by
  rw [H3ZornJordanQuadraticReconstruction]
  change
    (1 / 2 : ℝ) • T y 1 (T y 1 x) -
        (1 / 4 : ℝ) • T (T y 1 y) 1 x =
      (2 : ℝ) •
          candidateJordanMul y (candidateJordanMul y x) -
        candidateJordanMul (candidateJordanMul y y) x
  simp only [candidateJordanMul, T_smul_left, T_smul_right, smul_smul]
  module

/-- Peirce-zero is closed under the native Jordan product.  This is the
coordinate form of `V₀(e₁) ∘ V₀(e₁) ⊆ V₀(e₁)`. -/
theorem jordanMul_preserves_peirceZero
    {X Y : H3Zorn ℝ} (hX : InPeirceZero X) (hY : InPeirceZero Y) :
    InPeirceZero (X * Y) := by
  rcases hX with ⟨hX1, hXa, hXc⟩
  rcases hY with ⟨hY1, hYa, hYc⟩
  change InPeirceZero (candidateJordanMul X Y)
  rw [candidateJordanMul_trace_formula]
  refine ⟨?_, ?_, ?_⟩
  · simp [InPeirceZero, H3Zorn.linearTrace, H3Zorn.crossProduct,
      H3Zorn.adjointQuad, H3Zorn.add_readback, H3Zorn.sub_readback,
      H3Zorn.smul_readback, hX1, hXa, hXc, hY1, hYa, hYc,
      ZornVectorMatrix.zero, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.cross]
  · ext i
    simp [InPeirceZero, H3Zorn.linearTrace, H3Zorn.crossProduct,
      H3Zorn.adjointQuad, H3Zorn.add_readback, H3Zorn.sub_readback,
      H3Zorn.smul_readback, hX1, hXa, hXc, hY1, hYa, hYc,
      ZornVectorMatrix.zero, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.cross]
  · ext i
    simp [InPeirceZero, H3Zorn.linearTrace, H3Zorn.crossProduct,
      H3Zorn.adjointQuad, H3Zorn.add_readback, H3Zorn.sub_readback,
      H3Zorn.smul_readback, hX1, hXa, hXc, hY1, hYa, hYc,
      ZornVectorMatrix.zero, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.cross]

/-- The quadratic Jordan representation preserves `V₀(e₁)`. -/
theorem U_preserves_peirceZero
    {y x : H3Zorn ℝ} (hy : InPeirceZero y) (hx : InPeirceZero x) :
    InPeirceZero (H3Zorn.U y x) := by
  rw [U_eq_jordan_quadratic]
  rcases hy with ⟨hy1, hya, hyc⟩
  rcases hx with ⟨hx1, hxa, hxc⟩
  have hy' : InPeirceZero y := ⟨hy1, hya, hyc⟩
  have hx' : InPeirceZero x := ⟨hx1, hxa, hxc⟩
  have hyx : InPeirceZero (y * x) :=
    jordanMul_preserves_peirceZero hy' hx'
  have hyyx : InPeirceZero (y * (y * x)) :=
    jordanMul_preserves_peirceZero hy' hyx
  have hyy : InPeirceZero (y * y) :=
    jordanMul_preserves_peirceZero hy' hy'
  have hyy_x : InPeirceZero ((y * y) * x) :=
    jordanMul_preserves_peirceZero hyy hx'
  rcases hyyx with ⟨h1, ha, hc⟩
  rcases hyy_x with ⟨k1, ka, kc⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [InPeirceZero, H3Zorn.sub_readback, H3Zorn.smul_readback, h1, k1]
  · ext i
    simp [InPeirceZero, H3Zorn.sub_readback, H3Zorn.smul_readback,
      ha, ka, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i
    simp [InPeirceZero, H3Zorn.sub_readback, H3Zorn.smul_readback,
      hc, kc, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]

/-- The induced ten-dimensional quadratic representation on the native
transversal coordinate carrier. -/
def U10 (u v : PeirceZeroCoord) : PeirceZeroCoord :=
  let X := H3Zorn.U (peirceZeroEmbed u) (peirceZeroEmbed v)
  ((X.α₂, X.α₃), X.b)

/-- The Peirce-zero coordinate embedding strictly intertwines the induced
10-dimensional operator with the ambient split-Albert `U`-operator. -/
theorem peirceZeroEmbed_intertwines_U10 (u v : PeirceZeroCoord) :
    peirceZeroEmbed (U10 u v) =
      H3Zorn.U (peirceZeroEmbed u) (peirceZeroEmbed v) := by
  apply peirceZeroEmbed_extract
  exact U_preserves_peirceZero (peirceZeroEmbed_mem u) (peirceZeroEmbed_mem v)

/-- Readback of the already-verified metric convention: the ten-dimensional
transversal quadratic form is the split `(5,5)` form. -/
theorem transversal_metric_is_q55 (p : PeirceZeroCoord) :
    h2SplitDet p.1.1 p.1.2 p.2 =
      q55Real (h2ToVec55 p.1.1 p.1.2 p.2) := by
  exact h2SplitDet_eq_q55Real p.1.1 p.1.2 p.2

end InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation
