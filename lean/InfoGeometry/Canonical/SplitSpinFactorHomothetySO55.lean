import Mathlib
import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
import InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.SplitSpinFactorHomothetySO55

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.BivectorVectorRepresentation

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev V10 := SplitSpacetime10

/-- Polar trace pairing of the split-octonion norm. -/
def zornPolar (x y : Zorn) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

@[simp] theorem zornPolar_symm (x y : Zorn) : zornPolar x y = zornPolar y x := by
  simp [zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVec3.dot, Fin.sum_univ_three]
  ring

@[simp] theorem zornPolar_self (x : Zorn) :
    zornPolar x x = 2 * ZornVectorMatrix.norm x := by
  simp [zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.norm,
    ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Quadratic polarization of the native split-octonion norm. -/
theorem zorn_norm_linear_combination
    (alpha beta : ℝ) (x y : Zorn) :
    ZornVectorMatrix.norm (alpha • x + beta • y) =
      alpha ^ 2 * ZornVectorMatrix.norm x +
      beta ^ 2 * ZornVectorMatrix.norm y +
      alpha * beta * zornPolar x y := by
  simp [zornPolar, ZornVectorMatrix.norm, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.smul, ZornVectorMatrix.add,
    ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Explicit spin-factor coordinate formula for the quadratic representation
on the fixed-`e1` ten-dimensional transversal. -/
def spinU10 (u v : V10) : V10 :=
  let tau := zornPolar u.2 v.2
  let Qu := splitInterval10 u
  let K := u.1.1 * v.1.1 + u.1.2 * v.1.2 + tau
  ((u.1.1 ^ 2 * v.1.1 + u.1.1 * tau + v.1.2 * ZornVectorMatrix.norm u.2,
    u.1.2 ^ 2 * v.1.2 + u.1.2 * tau + v.1.1 * ZornVectorMatrix.norm u.2),
    Qu • v.2 + K • u.2)

/-- The coordinate formula is exactly the quadratic operator induced from the
native split-Albert `U`-operator. -/
theorem U10_eq_spinU10 (u v : V10) :
    U10 u v = spinU10 u v := by
  rcases u with ⟨⟨u2, u3⟩, ux⟩
  rcases v with ⟨⟨v2, v3⟩, vx⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [U10, fromH3, peirceZeroEmbed, spinU10, splitInterval10,
        h2SplitDet, zornPolar, H3Zorn.U, H3Zorn.traceBilin,
        H3Zorn.crossProduct, H3Zorn.adjointQuad,
        H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
        ZornVectorMatrix.norm, ZornVectorMatrix.trace,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVectorMatrix.add, ZornVectorMatrix.sub,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;> ring
  · apply ZornVectorMatrix.ext
    · simp [U10, fromH3, peirceZeroEmbed, spinU10, splitInterval10,
        h2SplitDet, zornPolar, H3Zorn.U, H3Zorn.traceBilin,
        H3Zorn.crossProduct, H3Zorn.adjointQuad,
        H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
        ZornVectorMatrix.norm, ZornVectorMatrix.trace,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVectorMatrix.add, ZornVectorMatrix.sub,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;> ring
    · funext i
      fin_cases i <;>
        simp [U10, fromH3, peirceZeroEmbed, spinU10, splitInterval10,
          h2SplitDet, zornPolar, H3Zorn.U, H3Zorn.traceBilin,
          H3Zorn.crossProduct, H3Zorn.adjointQuad,
          H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
          ZornVectorMatrix.norm, ZornVectorMatrix.trace,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj,
          ZornVectorMatrix.add, ZornVectorMatrix.sub,
          ZornVectorMatrix.neg, ZornVectorMatrix.smul,
          ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three] <;> ring
    · funext i
      fin_cases i <;>
        simp [U10, fromH3, peirceZeroEmbed, spinU10, splitInterval10,
          h2SplitDet, zornPolar, H3Zorn.U, H3Zorn.traceBilin,
          H3Zorn.crossProduct, H3Zorn.adjointQuad,
          H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
          ZornVectorMatrix.norm, ZornVectorMatrix.trace,
          ZornVectorMatrix.mul, ZornVectorMatrix.conj,
          ZornVectorMatrix.add, ZornVectorMatrix.sub,
          ZornVectorMatrix.neg, ZornVectorMatrix.smul,
          ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three] <;> ring
    · simp [U10, fromH3, peirceZeroEmbed, spinU10, splitInterval10,
        h2SplitDet, zornPolar, H3Zorn.U, H3Zorn.traceBilin,
        H3Zorn.crossProduct, H3Zorn.adjointQuad,
        H3Zorn.add_readback, H3Zorn.sub_readback, H3Zorn.smul_readback,
        ZornVectorMatrix.norm, ZornVectorMatrix.trace,
        ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVectorMatrix.add, ZornVectorMatrix.sub,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;> ring

/-- Fundamental spin-factor norm similitude. -/
theorem splitInterval10_spinU10_homothety (u v : V10) :
    splitInterval10 (spinU10 u v) =
      (splitInterval10 u) ^ 2 * splitInterval10 v := by
  rcases u with ⟨⟨u2, u3⟩, ux⟩
  rcases v with ⟨⟨v2, v3⟩, vx⟩
  simp only [spinU10, splitInterval10, h2SplitDet]
  rw [zorn_norm_linear_combination]
  rw [zornPolar_symm vx ux]
  ring

/-- Main theorem: the native induced quadratic representation is a quadratic
similitude of the split `(5,5)` determinant. -/
theorem splitInterval10_U10_homothety (u v : V10) :
    splitInterval10 (U10 u v) =
      (splitInterval10 u) ^ 2 * splitInterval10 v := by
  rw [U10_eq_spinU10]
  exact splitInterval10_spinU10_homothety u v

/-- Unit positive split norm gives exact quadratic-form preservation. -/
theorem U10_isometry_of_interval_one
    (u v : V10) (hu : splitInterval10 u = 1) :
    splitInterval10 (U10 u v) = splitInterval10 v := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- Unit negative split norm also gives exact quadratic-form preservation. -/
theorem U10_isometry_of_interval_neg_one
    (u v : V10) (hu : splitInterval10 u = -1) :
    splitInterval10 (U10 u v) = splitInterval10 v := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- A null parameter sends every vector into the null cone at the level of the
quadratic form.  No rank-one image claim is made here. -/
theorem U10_null_image_is_null
    (u v : V10) (hu : splitInterval10 u = 0) :
    splitInterval10 (U10 u v) = 0 := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- The native orthogonal Lie algebra already has the expected dimension 45. -/
theorem native_so55_finrank :
    Module.finrank ℝ So55 = 45 :=
  so55_finrank

/-- The type-D5 TKK owner is Lie-equivalent to the native split orthogonal
algebra and has the same dimension. -/
theorem native_tkk_typeD_finrank :
    Module.finrank ℝ TKKTypeD = 45 :=
  tkk_typeD_finrank

/-- Existing Clifford bivector generators are infinitesimally skew for the
native split quadratic form. -/
theorem native_bivector_generator_skew
    (u v w1 w2 : V55) :
    QuadraticMap.polar (⇑Q55) (bivectorVectorTransform u v w1) w2 +
      QuadraticMap.polar (⇑Q55) w1 (bivectorVectorTransform u v w2) = 0 :=
  bivectorVectorTransform_skew u v w1 w2

/-- Existing Clifford brackets act by commutators of the corresponding vector
transformations. -/
theorem native_bivector_bracket_action
    (u1 v1 u2 v2 w : V55) :
    ⁅⁅ι55 u1 * ι55 v1, ι55 u2 * ι55 v2⁆, ι55 w⁆ =
      ι55 (bivectorVectorTransform u1 v1 (bivectorVectorTransform u2 v2 w) -
        bivectorVectorTransform u2 v2 (bivectorVectorTransform u1 v1 w)) :=
  bivector_bracket_vector_action u1 v1 u2 v2 w

end InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
