import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

import InfoGeometry.Architecture.CartanCosetManifold
import InfoGeometry.Architecture.SymmetricSpace
import InfoGeometry.Canonical.AmplituhedronGrassmannianBCFWCapstone
import InfoGeometry.Canonical.ArnoldCohenPluckerBridge
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Twistor.TwoTwistorPlucker

/-!
# Grassmannian / Cartan / differential-form interoperability

This module adds theorem-level bridges between already existing owners:

* the matrix-chart Plucker minors used for `Gr(2,4)`;
* the repository's two six-coordinate Plucker conventions;
* the Klein-quadric decomposability condition;
* the homogeneous Cartan quotient `G / K` and the fixed subgroup of an involution;
* Mathlib's genuine exterior derivative on the `2 x 4` Grassmannian matrix chart.

No new geometric identification is assumed.  In particular, this file does not
claim that the matrix chart is already the quotient Grassmannian, nor does it
postulate a Maurer-Cartan equation for a Lie-group-valued differential form.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrassmannianCartanInteroperability

open Matrix
open InfoGeometry.Architecture
open InfoGeometry.Architecture.CartanCoset
open InfoGeometry.Canonical.AmplituhedronBCFW
open InfoGeometry.Canonical.ArnoldCohenPluckerBridge
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.TwoTwistorPlucker

/-! ## 1. Exact conversion between the two Plucker coordinate conventions -/

variable {R : Type*} [CommRing R]

/--
Convert the canonical `01,02,03,12,13,23` Plucker convention to the
`12,13,14,23,24,34` convention used by the Arnold-Cohen bridge.
-/
def arnoldCoordinatesOfPlucker6
    (P : Plucker6 R) :
    PluckerCoordinates R where
  p12 := P.p01
  p13 := P.p02
  p14 := P.p03
  p23 := P.p12
  p24 := P.p13
  p34 := P.p23

/-- The coordinate conversion preserves the Klein quadratic polynomial exactly. -/
theorem kleinQuadric_arnoldCoordinatesOfPlucker6
    (P : Plucker6 R) :
    kleinQuadric (arnoldCoordinatesOfPlucker6 P) = kleinQ P := by
  rfl

/-- A canonical Plucker vector on the Klein quadric is on-shell in the Arnold convention. -/
theorem isOnShellBoundary_of_kleinQ_zero
    (P : Plucker6 R)
    (hP : kleinQ P = 0) :
    IsOnShellBoundary (arnoldCoordinatesOfPlucker6 P) := by
  unfold IsOnShellBoundary
  rw [kleinQuadric_arnoldCoordinatesOfPlucker6]
  exact hP

/-- Every decomposable bivector `X wedge Y` lands on the Arnold Klein boundary. -/
theorem pluckerLine_isOnShellBoundary
    (X Y : Vec4 R) :
    IsOnShellBoundary
      (arnoldCoordinatesOfPlucker6 (pluckerLine X Y)) := by
  exact isOnShellBoundary_of_kleinQ_zero
    (pluckerLine X Y) (kleinQ_pluckerLine X Y)

/-! ## 2. Matrix-chart Grassmannian minors -> canonical Plucker six-vector -/

/-- The six `2 x 2` minors of a `2 x 4` matrix in canonical Klein order. -/
def plucker6OfMatrix
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    Plucker6 ℝ where
  p01 := pluckerMinor C 0 1
  p02 := pluckerMinor C 0 2
  p03 := pluckerMinor C 0 3
  p12 := pluckerMinor C 1 2
  p13 := pluckerMinor C 1 3
  p23 := pluckerMinor C 2 3

/--
Left multiplication by a `2 x 2` matrix scales every Plucker minor by its determinant.

This is the exact algebraic covariance underlying the projective row-space description
of `Gr(2,4)`.
-/
theorem pluckerMinor_left_mul
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (i j : Fin 4) :
    pluckerMinor (A * C) i j =
      A.det * pluckerMinor C i j := by
  simp [pluckerMinor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- The full six-vector transforms projectively under row operations. -/
theorem plucker6OfMatrix_left_mul
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    plucker6OfMatrix (A * C) =
      Plucker6.scale A.det (plucker6OfMatrix C) := by
  apply Plucker6.ext <;>
    simp [plucker6OfMatrix, Plucker6.scale, pluckerMinor_left_mul]

/-- The six minors of every `2 x 4` matrix satisfy the Klein-Plucker quadric. -/
theorem kleinQ_plucker6OfMatrix
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    kleinQ (plucker6OfMatrix C) = 0 := by
  simpa [plucker6OfMatrix, kleinQ] using
    (plucker_syzygy C (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))

/-- Matrix-chart Plucker coordinates therefore land on the Arnold on-shell boundary. -/
theorem matrixChart_isOnShellBoundary
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    IsOnShellBoundary
      (arnoldCoordinatesOfPlucker6 (plucker6OfMatrix C)) := by
  exact isOnShellBoundary_of_kleinQ_zero
    (plucker6OfMatrix C) (kleinQ_plucker6OfMatrix C)

/--
If the row operation has determinant one, the canonical Plucker six-vector is
strictly invariant rather than merely projectively covariant.
-/
theorem plucker6OfMatrix_left_mul_det_one
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hA : A.det = 1) :
    plucker6OfMatrix (A * C) = plucker6OfMatrix C := by
  rw [plucker6OfMatrix_left_mul, hA]
  apply Plucker6.ext <;> simp [Plucker6.scale]

/-! ## 3. Twistor decomposability -> the same on-shell Plucker owner -/

/-- The existing two-twistor Plucker construction lands in the Arnold Klein boundary. -/
theorem twistorPair_isOnShellBoundary
    (Z₁ Z₂ : Twistor4) :
    IsOnShellBoundary
      (arnoldCoordinatesOfPlucker6 (twistorPairPlucker Z₁ Z₂)) := by
  exact isOnShellBoundary_of_kleinQ_zero
    (twistorPairPlucker Z₁ Z₂)
    (twistorPairPlucker_on_klein Z₁ Z₂)

/-! ## 4. Cartan fixed subgroup -> homogeneous-space stabilizer -/

/--
For the canonical homogeneous space attached to a Cartan involution, the stabilizer
of the origin is exactly the fixed-point subgroup of that involution.
-/
theorem cartan_fixedSubgroup_stabilizer_origin
    {G : Type*} [Group G]
    (θ : CartanInvolution G)
    (g : G) :
    leftAction θ.fixedSubgroup g (origin θ.fixedSubgroup) =
        origin θ.fixedSubgroup ↔
      θ.toMulAut g = g := by
  rw [stabilizer_origin_eq]
  exact θ.mem_fixedSubgroup_iff g

/--
The same statement for an arbitrary repository `SymmetricPair`: the subgroup
carried by the pair is precisely the isotropy subgroup at the quotient origin.
-/
theorem symmetricPair_stabilizer_origin
    {G : Type*} [Group G]
    (S : SymmetricPair G)
    (g : G) :
    leftAction S.K g (origin S.K) = origin S.K ↔
      S.θ.toMulAut g = g := by
  rw [stabilizer_origin_eq]
  exact S.fix_eq g

/-! ## 5. Genuine Mathlib differential forms on the Grassmannian matrix chart -/

/-- The finite `2 x 4` matrix chart used by the Grassmannian lane. -/
abbrev GrassmannianMatrixChart :=
  Matrix (Fin 2) (Fin 4) ℝ

/-- Genuine Mathlib differential forms on the matrix chart. -/
abbrev GrassmannianDifferentialForm (n : ℕ) :=
  GrassmannianMatrixChart →
    GrassmannianMatrixChart [⋀^Fin n]→L[ℝ] ℝ

/-- Exterior derivative on the Grassmannian matrix chart. -/
noncomputable def grassmannianExteriorDerivative
    {n : ℕ}
    (ω : GrassmannianDifferentialForm n) :
    GrassmannianDifferentialForm (n + 1) :=
  extDeriv ω

/-- The exterior derivative squares to zero on `C^2` forms on the matrix chart. -/
theorem grassmannianExteriorDerivative_sq_zero
    {n : ℕ}
    (ω : GrassmannianDifferentialForm n)
    (hω : ContDiff ℝ 2 ω) :
    grassmannianExteriorDerivative
      (grassmannianExteriorDerivative ω) = 0 := by
  exact extDeriv_extDeriv hω (by simp)

/-- Pointwise form of `d^2 = 0`. -/
theorem grassmannianExteriorDerivative_sq_zero_apply
    {n : ℕ}
    (ω : GrassmannianDifferentialForm n)
    (hω : ContDiff ℝ 2 ω)
    (C : GrassmannianMatrixChart) :
    grassmannianExteriorDerivative
      (grassmannianExteriorDerivative ω) C = 0 := by
  rw [grassmannianExteriorDerivative_sq_zero ω hω]
  rfl

end InfoGeometry.Canonical.GrassmannianCartanInteroperability
