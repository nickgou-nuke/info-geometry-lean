import Mathlib
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace

noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ

/-- Coordinate carrier of the Peirce-1 ray at the primitive diagonal idempotent. -/
abbrev PeirceOneCoord := ℝ

/-- Coordinate carrier of the two split-octonionic Peirce-1/2 slots. -/
abbrev PeirceHalfCoord := Zorn × Zorn

/-- Coordinate carrier of the transversal Hermitian 2x2 split-octonion block. -/
abbrev PeirceZeroCoord := (ℝ × ℝ) × Zorn

/-- The first primitive diagonal idempotent `diag(1,0,0)`. -/
def e1 : H3Zorn ℝ := h3_diag₁

/-- Boundary ray based at `diag(lambda,1,1)`. -/
def boundaryPoint (lambda : ℝ) : H3Zorn ℝ :=
  { α₁ := lambda, α₂ := 1, α₃ := 1, a := 0, b := 0, c := 0 }

/-- Peirce-1 coordinate embedding. -/
def peirceOneEmbed (r : PeirceOneCoord) : H3Zorn ℝ :=
  { α₁ := r, α₂ := 0, α₃ := 0, a := 0, b := 0, c := 0 }

/-- Peirce-1/2 coordinate embedding: the `(1,2)` and `(3,1)` slots. -/
def peirceHalfEmbed (p : PeirceHalfCoord) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := p.1, b := 0, c := p.2 }

/-- Peirce-0 coordinate embedding: the lower-right Hermitian 2x2 block. -/
def peirceZeroEmbed (p : PeirceZeroCoord) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := p.1.1, α₃ := p.1.2, a := 0, b := p.2, c := 0 }

/-- Exact coordinate decomposition `27 = 1 + 16 + 10` at `e1`. -/
theorem peirce_reconstruction (X : H3Zorn ℝ) :
    peirceOneEmbed X.α₁ + peirceHalfEmbed (X.a, X.c) +
        peirceZeroEmbed ((X.α₂, X.α₃), X.b) = X := by
  apply H3Zorn.ext_h3 <;>
    simp [peirceOneEmbed, peirceHalfEmbed, peirceZeroEmbed,
      H3Zorn.add_readback, ZornVectorMatrix.add, ZornVectorMatrix.zero]

/-- The native split-octonion coordinate carrier has real dimension eight. -/
theorem zorn_finrank_eq_eight : Module.finrank ℝ Zorn = 8 := by
  rw [Module.finrank_eq_card_basis InfoGeometry.Algebra.zornCoordinateBasis]
  simp

/-- Dimensions of the three fixed-idempotent coordinate sectors. -/
theorem peirce_coordinate_finranks :
    Module.finrank ℝ PeirceOneCoord = 1 ∧
    Module.finrank ℝ PeirceHalfCoord = 16 ∧
    Module.finrank ℝ PeirceZeroCoord = 10 := by
  constructor
  · simp [PeirceOneCoord]
  constructor
  · rw [Module.finrank_prod, zorn_finrank_eq_eight, zorn_finrank_eq_eight]
    norm_num
  · rw [Module.finrank_prod, Module.finrank_prod, zorn_finrank_eq_eight]
    norm_num

/-- The cubic norm on the boundary ray is exactly the ray coordinate. -/
@[simp] theorem normCubic_boundaryPoint (lambda : ℝ) :
    H3Zorn.normCubic (boundaryPoint lambda) = lambda := by
  simp [boundaryPoint, H3Zorn.normCubic, ZornVectorMatrix.zero,
    ZornVectorMatrix.norm, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVec3.dot, ZornVec3.cross]

/-- Quadratic determinant of the transversal Hermitian `2 x 2` split block. -/
def h2SplitDet (d2 d3 : ℝ) (b : Zorn) : ℝ :=
  d2 * d3 - ZornVectorMatrix.norm b

/-- Anchoring a transversal block at the first diagonal coordinate factors the
split-Albert cubic norm into `lambda` times the `H2(O_s)` determinant. -/
theorem normCubic_transversal_factorization
    (lambda d2 d3 : ℝ) (b : Zorn) :
    H3Zorn.normCubic
      ({ α₁ := lambda, α₂ := d2, α₃ := d3, a := 0, b := b, c := 0 } : H3Zorn ℝ) =
      lambda * h2SplitDet d2 d3 b := by
  simp [H3Zorn.normCubic, h2SplitDet, ZornVectorMatrix.zero,
    ZornVectorMatrix.norm, ZornVectorMatrix.zero_mul,
    ZornVectorMatrix.mul_zero, ZornVectorMatrix.trace_zero]
  ring

/-- Diagonal `(5,5)` coordinates of the transversal `H2(O_s)` determinant. -/
def h2ToVec55 (d2 d3 : ℝ) (z : Zorn) : Fin 10 → ℝ :=
  ![(d2 + d3) / 2,
    (z.a - z.b) / 2,
    (z.v 0 + z.w 0) / 2,
    (z.v 1 + z.w 1) / 2,
    (z.v 2 + z.w 2) / 2,
    (d2 - d3) / 2,
    (z.a + z.b) / 2,
    (z.v 0 - z.w 0) / 2,
    (z.v 1 - z.w 1) / 2,
    (z.v 2 - z.w 2) / 2]

/-- Standard diagonal quadratic form of signature `(5,5)` in ten coordinates. -/
def q55Real (v : Fin 10 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 -
    v 5 ^ 2 - v 6 ^ 2 - v 7 ^ 2 - v 8 ^ 2 - v 9 ^ 2

/-- The transversal determinant is the split `(5,5)` quadratic form.
In particular, this owner does not identify the split transversal block with
Lorentzian `(1,9)` Minkowski space. -/
theorem h2SplitDet_eq_q55Real
    (d2 d3 : ℝ) (z : Zorn) :
    h2SplitDet d2 d3 z = q55Real (h2ToVec55 d2 d3 z) := by
  simp [h2SplitDet, q55Real, h2ToVec55, ZornVectorMatrix.norm,
    ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Pure longitudinal variation through `diag(lambda,1,1)`. -/
def longitudinalCurve (lambda r t : ℝ) : H3Zorn ℝ :=
  { α₁ := lambda + t * r, α₂ := 1, α₃ := 1, a := 0, b := 0, c := 0 }

/-- Exact longitudinal cubic germ. -/
theorem normCubic_longitudinalCurve (lambda r t : ℝ) :
    H3Zorn.normCubic (longitudinalCurve lambda r t) = lambda + t * r := by
  simp [longitudinalCurve, H3Zorn.normCubic, ZornVectorMatrix.zero,
    ZornVectorMatrix.norm, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVec3.dot, ZornVec3.cross]

/-- Pure Peirce-1/2 variation through `diag(lambda,1,1)`. -/
def halfCurve (lambda t : ℝ) (a c : Zorn) : H3Zorn ℝ :=
  { α₁ := lambda, α₂ := 1, α₃ := 1,
    a := t • a, b := 0, c := t • c }

/-- Exact Peirce-1/2 cubic germ.  The second-order coefficient is the
indefinite split-octonion norm, scaled by `lambda^{-1}` after applying `-log`. -/
theorem normCubic_halfCurve (lambda t : ℝ) (a c : Zorn) :
    H3Zorn.normCubic (halfCurve lambda t a c) =
      lambda - t ^ 2 * (ZornVectorMatrix.norm a + ZornVectorMatrix.norm c) := by
  simp [halfCurve, H3Zorn.normCubic, ZornVectorMatrix.norm_smul,
    ZornVectorMatrix.zero, ZornVectorMatrix.zero_mul,
    ZornVectorMatrix.mul_zero, ZornVectorMatrix.trace_zero]
  ring

/-- Pure transversal variation through `diag(lambda,1,1)`. -/
def zeroCurve (lambda t d2 d3 : ℝ) (b : Zorn) : H3Zorn ℝ :=
  { α₁ := lambda, α₂ := 1 + t * d2, α₃ := 1 + t * d3,
    a := 0, b := t • b, c := 0 }

/-- Exact transversal cubic germ.  Its coefficients remain finite as
`lambda -> 0`, but the underlying split quadratic form is not positive. -/
theorem normCubic_zeroCurve (lambda t d2 d3 : ℝ) (b : Zorn) :
    H3Zorn.normCubic (zeroCurve lambda t d2 d3 b) =
      lambda *
        (1 + t * (d2 + d3) + t ^ 2 * (d2 * d3 - ZornVectorMatrix.norm b)) := by
  simp [zeroCurve, H3Zorn.normCubic, ZornVectorMatrix.norm_smul,
    ZornVectorMatrix.zero, ZornVectorMatrix.zero_mul,
    ZornVectorMatrix.mul_zero, ZornVectorMatrix.trace_zero]
  ring

/-- Algebraic second-variation coefficient of `-log` in the Peirce-1/2
sector, obtained from the exact quadratic germ above. -/
def halfBarrierSecondCoeff (lambda : ℝ) (a c : Zorn) : ℝ :=
  2 * (ZornVectorMatrix.norm a + ZornVectorMatrix.norm c) / lambda

/-- Algebraic second-variation coefficient of the transversal log germ at the
identity of the lower-right block. -/
def zeroBarrierSecondCoeff (d2 d3 : ℝ) (b : Zorn) : ℝ :=
  d2 ^ 2 + d3 ^ 2 + 2 * ZornVectorMatrix.norm b

/-- A concrete negative-norm split-octonion direction. -/
def negativeNormZorn : Zorn :=
  { a := 0, v := ZornVec3.basis 0, w := ZornVec3.basis 0, b := 0 }

@[simp] theorem norm_negativeNormZorn :
    ZornVectorMatrix.norm negativeNormZorn = -1 := by
  simp [negativeNormZorn, ZornVectorMatrix.norm, ZornVec3.dot,
    ZornVec3.basis, Fin.sum_univ_three]

/-- The split Peirce-1/2 second-variation form is genuinely indefinite.
Hence the split-Albert cubic carrier does not by itself supply a positive
Dikin/Riemannian metric. -/
theorem halfBarrierSecondCoeff_can_be_negative
    {lambda : ℝ} (hlambda : 0 < lambda) :
    halfBarrierSecondCoeff lambda negativeNormZorn 0 < 0 := by
  simp [halfBarrierSecondCoeff, hlambda]

/-- The transversal second-variation form is also indefinite. -/
theorem zeroBarrierSecondCoeff_can_be_negative :
    zeroBarrierSecondCoeff 0 0 negativeNormZorn < 0 := by
  simp [zeroBarrierSecondCoeff]

end InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
