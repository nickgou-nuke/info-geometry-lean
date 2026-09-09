import Mathlib
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticHomothety

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev V10 := SplitSpacetime10

/-- Polar form of the split-octonion composition norm, in the repository's
native trace-times-conjugate convention. -/
def zornPolar (x y : Zorn) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

/-- The native split-octonion polar form is symmetric. -/
theorem zornPolar_comm (x y : Zorn) :
    zornPolar x y = zornPolar y x := by
  exact ZornVectorMatrix.trace_mul_conj_comm x y

/-- Diagonal polarization recovers twice the quadratic norm. -/
theorem zornPolar_self (x : Zorn) :
    zornPolar x x = 2 * ZornVectorMatrix.norm x := by
  simp [zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.norm, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

/-- Quadratic polarization of the native split-octonion norm.  This is the
coordinate-free scalar lemma used by the ten-dimensional homothety proof. -/
theorem zorn_norm_smul_add_smul
    (a b : ℝ) (x y : Zorn) :
    ZornVectorMatrix.norm (a • x + b • y) =
      a ^ 2 * ZornVectorMatrix.norm x +
      b ^ 2 * ZornVectorMatrix.norm y +
      a * b * zornPolar x y := by
  simp [zornPolar, ZornVectorMatrix.norm, ZornVectorMatrix.smul,
    ZornVectorMatrix.add, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.trace, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Explicit spin-factor coordinate normal form of the already-defined native
quadratic representation `U10`.  No second quadratic operator is introduced. -/
def U10Coordinate (u v : V10) : V10 :=
  let tau := zornPolar u.2 v.2
  let qu := splitInterval10 u
  let k := u.1.1 * v.1.1 + u.1.2 * v.1.2 + tau
  ((u.1.1 ^ 2 * v.1.1 + u.1.1 * tau + v.1.2 * ZornVectorMatrix.norm u.2,
    u.1.2 ^ 2 * v.1.2 + u.1.2 * tau + v.1.1 * ZornVectorMatrix.norm u.2),
   qu • v.2 + k • u.2)

/-- The native McCrimmon/Freudenthal `U10` agrees with the standard
`H₂(O_s)` spin-factor coordinate formula. -/
theorem U10_eq_coordinate (u v : V10) :
    U10 u v = U10Coordinate u v := by
  rcases u with ⟨⟨u2, u3⟩, z⟩
  rcases v with ⟨⟨v2, v3⟩, w⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [U10, fromH3, peirceZeroEmbed, U10Coordinate, zornPolar,
        splitInterval10, h2SplitDet, H3Zorn.U, H3Zorn.traceBilin,
        H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.add_readback,
        H3Zorn.sub_readback, H3Zorn.smul_readback,
        ZornVectorMatrix.norm, ZornVectorMatrix.trace,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVectorMatrix.add, ZornVectorMatrix.sub,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · ext i
    fin_cases i <;>
      simp [U10, fromH3, peirceZeroEmbed, U10Coordinate, zornPolar,
        splitInterval10, h2SplitDet, H3Zorn.U, H3Zorn.traceBilin,
        H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.add_readback,
        H3Zorn.sub_readback, H3Zorn.smul_readback,
        ZornVectorMatrix.norm, ZornVectorMatrix.trace,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVectorMatrix.add, ZornVectorMatrix.sub,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring

/-- Main quadratic-similitude theorem on the fixed-`e1` ten-dimensional
Peirce-zero sector:

`Q(U_u v) = Q(u)^2 Q(v)`.

The quadratic form is the already-certified split `(5,5)` determinant. -/
theorem splitInterval10_U10_homothety (u v : V10) :
    splitInterval10 (U10 u v) =
      splitInterval10 u ^ 2 * splitInterval10 v := by
  rw [U10_eq_coordinate]
  rcases u with ⟨⟨u2, u3⟩, z⟩
  rcases v with ⟨⟨v2, v3⟩, w⟩
  simp only [U10Coordinate, splitInterval10, h2SplitDet]
  rw [zorn_norm_smul_add_smul]
  rw [zornPolar_comm w z]
  ring

/-- Unit split norm gives an exact isometry of the certified `(5,5)`
quadratic form.  This is an isometry statement, not yet a surjectivity or
full-group classification theorem. -/
theorem splitInterval10_U10_isometry_of_unit
    (u v : V10) (hu : splitInterval10 u = 1) :
    splitInterval10 (U10 u v) = splitInterval10 v := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- Split norm `-1` also yields an exact quadratic-form isometry because the
similitude factor is the square of the norm. -/
theorem splitInterval10_U10_isometry_of_neg_unit
    (u v : V10) (hu : splitInterval10 u = -1) :
    splitInterval10 (U10 u v) = splitInterval10 v := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- A null parameter sends every vector into the null cone.  This theorem
asserts only nullity of the image; it does not assert that the image is the
one-dimensional ray spanned by the parameter. -/
theorem splitInterval10_U10_null_image
    (u v : V10) (hu : splitInterval10 u = 0) :
    splitInterval10 (U10 u v) = 0 := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- The homothety theorem transported to the diagonal `Fin 10` `(5,5)`
quadratic readout already owned by the Peirce boundary layer. -/
theorem q55Real_U10_readout (u v : V10) :
    q55Real
        (h2ToVec55 (U10 u v).1.1 (U10 u v).1.2 (U10 u v).2) =
      splitInterval10 u ^ 2 *
        q55Real (h2ToVec55 v.1.1 v.1.2 v.2) := by
  rw [← splitInterval10_eq_q55Real (U10 u v),
    splitInterval10_U10_homothety,
    splitInterval10_eq_q55Real]

end InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticHomothety
