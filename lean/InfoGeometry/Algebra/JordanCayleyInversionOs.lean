import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.OperatorAlgebra.SplitOctonionNormComposition
import Mathlib.Tactic

/-!
# Concrete split-octonion determinant and trace-reversal coordinate packet

This file records theorem-safe finite coordinate identities for the Zorn
split-octonion model over `ℤ` and a rational `J₂(O_s)` determinant packet.

It uses the existing norm-composition theorem as navigation/context, but does
not prove a full octonionic matrix inverse, a Jordan triple theorem, a CCC
statement, or a `Spin(5,5)`/structure-group isomorphism.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.NormComposition

namespace InfoGeometry.Algebra.JordanCayleyInversionOs

/-- Zorn norm lifted to ℚ. -/
def zornNormℚ (Z : SplitOct) : ℚ :=
  ((Z.a : ℚ) * (Z.b : ℚ)) -
    ((Z.x0 : ℚ) * (Z.y0 : ℚ) + (Z.x1 : ℚ) * (Z.y1 : ℚ) + (Z.x2 : ℚ) * (Z.y2 : ℚ))

/-- Existing split-octonion norm-composition identity, re-exported locally. -/
theorem detZ_mulZ_composition (X Y : SplitOct) :
    InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ (mulZ X Y) =
      InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ X *
        InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ Y :=
  detZ_mulZ X Y

/--
A Hermitian 2×2 matrix over the split octonions 𝕆_s (Zorn representation):

    X = [[ξ₊, Z], [conj(Z), ξ₋]]

where `ξ₊, ξ₋ ∈ ℚ` are the light-cone coordinates and `Z ∈ 𝕆_s` encodes
the 8 bulk coordinates.
-/
structure Herm2x2Os where
  xp : ℚ    -- ξ₊
  xm : ℚ    -- ξ₋
  z : SplitOct  -- Z ∈ 𝕆_s
  deriving DecidableEq, Repr

namespace Herm2x2Os

/-- Determinant: `det(X) = ξ₊·ξ₋ - ‖Z‖²`.  This is the (5,5) quadratic form. -/
def det (X : Herm2x2Os) : ℚ :=
  X.xp * X.xm - zornNormℚ X.z

/--
The split octonion conjugate in the Zorn representation.

    conj(a, x; y, b) = (b, -x; -y, a)

This satisfies `Z·conj(Z) = detZ(Z)·1` in the coordinate model.
-/
def octConj (Z : SplitOct) : SplitOct :=
  ⟨Z.b, Z.a, -Z.x0, -Z.x1, -Z.x2, -Z.y0, -Z.y1, -Z.y2⟩

/-- Diagonal scalar cell `t · 1` in the Zorn model. -/
def scalarOne (t : ℤ) : SplitOct :=
  ⟨t, t, 0, 0, 0, 0, 0, 0⟩

/-- The Zorn norm lifted to ℚ equals the ℚ-cast of `detZ`. -/
theorem zornNormℚ_eq_detZ_cast (Z : SplitOct) :
    zornNormℚ Z =
      (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ Z : ℚ) := by
  simp [zornNormℚ, InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ]

/-- Coordinate conjugation identity: `Z * conj(Z) = detZ(Z) · 1`. -/
theorem mul_conj_eq_det (Z : SplitOct) :
    mulZ Z (octConj Z) =
      scalarOne (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ Z) := by
  cases Z
  simp [octConj, scalarOne, InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.detZ, mulZ]
  repeat constructor <;> try ring_nf <;> trivial

/-- Integer coordinate scaling on the Zorn cell, viewed later through ℚ-casts. -/
def scaleZ (c : ℤ) (Z : SplitOct) : SplitOct :=
  ⟨c * Z.a, c * Z.b, c * Z.x0, c * Z.x1, c * Z.x2,
    c * Z.y0, c * Z.y1, c * Z.y2⟩

/-- Integer scaling of the mixed ℚ/ℤ Hermitian packet. -/
def scale (c : ℤ) (X : Herm2x2Os) : Herm2x2Os :=
  ⟨(c : ℚ) * X.xp, (c : ℚ) * X.xm, scaleZ c X.z⟩

/-- The lifted Zorn norm is quadratic under integer coordinate scaling. -/
theorem zornNormℚ_scaleZ (c : ℤ) (Z : SplitOct) :
    zornNormℚ (scaleZ c Z) = (c : ℚ) ^ 2 * zornNormℚ Z := by
  cases Z
  simp [scaleZ, zornNormℚ]
  ring

/-- The determinant equals the (5,5) quadratic form with explicit ℚ witnesses. -/
theorem det_eq_quadratic (X : Herm2x2Os) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : (X.z.a : ℚ) = x7 + x2) (hzb : (X.z.b : ℚ) = x7 - x2)
    (hzx0 : (X.z.x0 : ℚ) = x3 + x8) (hzy0 : (X.z.y0 : ℚ) = x3 - x8)
    (hzx1 : (X.z.x1 : ℚ) = x4 + x9) (hzy1 : (X.z.y1 : ℚ) = x4 - x9)
    (hzx2 : (X.z.x2 : ℚ) = x5 + x10) (hzy2 : (X.z.y2 : ℚ) = x5 - x10) :
    X.det = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 := by
  simp [det, zornNormℚ, hxp, hxm, hza, hzb, hzx0, hzy0, hzx1, hzy1, hzx2, hzy2]; ring

/--
**Trace reversal:** X̃ = [[ξ₋, -Z], [-conj(Z), ξ₊]].

In the Zorn model, -Z is `negZ Z`.
-/
def traceReversal (X : Herm2x2Os) : Herm2x2Os :=
  ⟨X.xm, X.xp, negZ X.z⟩

/-- Trace reversal is an involution on the concrete `J₂(O_s)` packet. -/
theorem traceReversal_involutive (X : Herm2x2Os) :
    traceReversal (traceReversal X) = X := by
  cases X with
  | mk xp xm z =>
    cases z
    simp [traceReversal, negZ]

/-- The determinant is invariant under trace reversal. -/
theorem det_traceReversal (X : Herm2x2Os) :
    det (traceReversal X) = det X := by
  cases X with
  | mk xp xm z =>
    cases z
    simp [det, traceReversal, zornNormℚ, negZ]
    ring

/-- Trace reversal commutes with integer coordinate scaling. -/
theorem traceReversal_scale (c : ℤ) (X : Herm2x2Os) :
    (scale c X).traceReversal = scale c X.traceReversal := by
  cases X with
  | mk xp xm z =>
    cases z
    simp [scale, traceReversal, scaleZ, negZ]

/-- The determinant is quadratic under integer coordinate scaling. -/
theorem det_scale (c : ℤ) (X : Herm2x2Os) :
    (scale c X).det = (c : ℚ) ^ 2 * X.det := by
  simp [scale, det, zornNormℚ_scaleZ]
  ring

/--
Result of the product `X · X̃` as diagonal components.
-/
structure ProdResult where
  e11 : ℚ
  e22 : ℚ

/-- Compute `X · X̃`.  The off-diagonal entries vanish by trace-reversal. -/
def mulTraceReversal (X : Herm2x2Os) : ProdResult :=
  { e11 := X.xp * X.xm - zornNormℚ X.z
    e22 := -(X.xp * X.xm - zornNormℚ X.z) }

/--
Coordinate trace-reversal determinant identity for the diagonal packet.

This is not a full octonionic matrix inverse theorem; it is the same finite
packet shape used for the `C_s` and `H_s` coordinate layers.
-/
theorem fundamental_identity (X : Herm2x2Os) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } := by
  simp [mulTraceReversal, det, zornNormℚ]

/--
**Corollary:** On the coordinate Klein quadric `{det(X) = 0}`, the diagonal
packet vanishes.
-/
theorem on_klein_quadric (X : Herm2x2Os) (h : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 := by
  have h1 : X.mulTraceReversal.e11 = X.det := by
    unfold mulTraceReversal det; rfl
  have h2 : X.mulTraceReversal.e22 = -X.det := by
    unfold mulTraceReversal det; rfl
  rw [h1, h2, h]
  simp

/--
Coordinate null equation for the rational determinant packet.
-/
theorem klein_quadric_equation (X : Herm2x2Os) :
    (X.det = 0) ↔ X.xp * X.xm = zornNormℚ X.z := by
  dsimp [det]
  constructor
  · intro h; linarith
  · intro h; linarith

/--
Parametric coordinate null equation for the split-octonionic `(5,5)` packet.
This is only a quadratic-coordinate identity; it does not prove a projective
Klein-quadric geometry, tiling-preservation theorem, or conformal inversion
statement.
-/
theorem klein_quadric_equation' (X : Herm2x2Os) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : (X.z.a : ℚ) = x7 + x2) (hzb : (X.z.b : ℚ) = x7 - x2)
    (hzx0 : (X.z.x0 : ℚ) = x3 + x8) (hzy0 : (X.z.y0 : ℚ) = x3 - x8)
    (hzx1 : (X.z.x1 : ℚ) = x4 + x9) (hzy1 : (X.z.y1 : ℚ) = x4 - x9)
    (hzx2 : (X.z.x2 : ℚ) = x5 + x10) (hzy2 : (X.z.y2 : ℚ) = x5 - x10) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 = 0 := by
  rw [det_eq_quadratic X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 hxp hxm hza hzb hzx0 hzy0 hzx1 hzy1 hzx2 hzy2]

end Herm2x2Os

end InfoGeometry.Algebra.JordanCayleyInversionOs
