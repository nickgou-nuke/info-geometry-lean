import Mathlib
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.H3ZornAlgebraicSoldering

noncomputable section

namespace InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ

/-- Native symmetric polar form of the split-octonion norm, written purely
on the Zorn carrier. -/
def zornPair (x y : Zorn) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

@[simp] theorem zornPair_comm (x y : Zorn) : zornPair x y = zornPair y x := by
  exact ZornVectorMatrix.trace_mul_conj_comm x y

/-- Independent Peirce/Zorn formula for the Jordan product on
`R^3 × O_s^3`.  This definition does not mention the installed `H3Zorn`
product and is therefore suitable for a non-tautological soldering theorem. -/
noncomputable def coordJordanMulExplicit (X Y : H3Coord) : H3Coord :=
  let x1 := X.1.1
  let x2 := X.1.2.1
  let x3 := X.1.2.2
  let a := X.2.1
  let b := X.2.2.1
  let c := X.2.2.2
  let y1 := Y.1.1
  let y2 := Y.1.2.1
  let y3 := Y.1.2.2
  let d := Y.2.1
  let e := Y.2.2.1
  let f := Y.2.2.2
  let half : ℝ := 1 / 2
  ((x1 * y1 + half * (zornPair a d + zornPair c f),
    (x2 * y2 + half * (zornPair a d + zornPair b e),
     x3 * y3 + half * (zornPair b e + zornPair c f))),
   (half •
      ((x1 + x2) • d + (y1 + y2) • a +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj c) (ZornVectorMatrix.conj e) +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj f) (ZornVectorMatrix.conj b)),
    (half •
      ((x2 + x3) • e + (y2 + y3) • b +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj a) (ZornVectorMatrix.conj f) +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj d) (ZornVectorMatrix.conj c)),
     half •
      ((x3 + x1) • f + (y3 + y1) • c +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj b) (ZornVectorMatrix.conj d) +
        ZornVectorMatrix.mul (ZornVectorMatrix.conj e) (ZornVectorMatrix.conj a)))))

/-- The explicit Peirce/Zorn formula solders exactly to the installed split
Albert Jordan product.  Unlike the earlier pullback definition of
`coordJordanMul`, this is a genuine intertwining theorem between independently
defined products. -/
theorem h3Soldering_explicitJordan_intertwines (X Y : H3Coord) :
    h3Soldering (coordJordanMulExplicit X Y) =
      h3Soldering X * h3Soldering Y := by
  rcases X with ⟨⟨x1, x2, x3⟩, ⟨a, b, c⟩⟩
  rcases Y with ⟨⟨y1, y2, y3⟩, ⟨d, e, f⟩⟩
  rw [← candidateJordanMul_eq_mul]
  rw [candidateJordanMul_trace_formula]
  apply H3Zorn.ext_h3
  all_goals
    simp only [coordJordanMulExplicit, h3Soldering_apply, zornPair,
      H3Zorn.linearTrace, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
      H3Zorn.one_readback,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.trace_add,
      ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul]
  · ring
  · ring
  · ring
  · module
  · module
  · module

/-- The independently defined explicit coordinate product agrees with the
older pullback product, now as a theorem rather than by definition. -/
theorem coordJordanMulExplicit_eq_coordJordanMul (X Y : H3Coord) :
    coordJordanMulExplicit X Y = coordJordanMul X Y := by
  apply h3Soldering.injective
  rw [h3Soldering_explicitJordan_intertwines,
    h3Soldering_jordan_intertwines]

/-- Genuine algebraic soldering datum based on the independent Peirce/Zorn
product. -/
noncomputable def h3ExplicitJordanSoldering :
    AlgebraicSoldering H3Coord (H3Zorn ℝ) where
  equiv := h3Soldering
  coordMul := coordJordanMulExplicit
  targetMul := fun x y => x * y
  map_mul := h3Soldering_explicitJordan_intertwines

end InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering
