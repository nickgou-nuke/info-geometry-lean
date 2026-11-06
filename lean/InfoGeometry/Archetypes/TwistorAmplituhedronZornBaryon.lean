/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Archetype XVIII: Twistor Plücker Coordinates, Grassmannian $\mathrm{Gr}(2,4)$, Klein Quadric, Zorn Split-Octonion, Nambu 3-Bracket & Amplituhedron 4-Bracket

Pure non-commutative matrix/operator algebra over `[Ring R]` (with commutative Grassmannian /
Plücker specialization over `[CommRing K]`). Zero `sorry`, zero axioms, and zero vacuous wrappers.
-/

namespace InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

/-- 3-vector over a ring `R`, used as the off-diagonal sector of Zorn matrices. -/
@[ext]
structure Vec3 (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Vec3
variable {R : Type*} [Ring R]

@[simp] def zero : Vec3 R := ⟨0, 0, 0⟩
instance instZeroVec3 : Zero (Vec3 R) := ⟨zero⟩

@[simp] lemma zero_x : (0 : Vec3 R).x = 0 := rfl
@[simp] lemma zero_y : (0 : Vec3 R).y = 0 := rfl
@[simp] lemma zero_z : (0 : Vec3 R).z = 0 := rfl

@[simp] def add (u v : Vec3 R) : Vec3 R := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
instance instAddVec3 : Add (Vec3 R) := ⟨add⟩

@[simp] lemma add_x (u v : Vec3 R) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : Vec3 R) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : Vec3 R) : (u + v).z = u.z + v.z := rfl

@[simp] def sub (u v : Vec3 R) : Vec3 R := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
instance instSubVec3 : Sub (Vec3 R) := ⟨sub⟩

@[simp] lemma sub_x (u v : Vec3 R) : (u - v).x = u.x - v.x := rfl
@[simp] lemma sub_y (u v : Vec3 R) : (u - v).y = u.y - v.y := rfl
@[simp] lemma sub_z (u v : Vec3 R) : (u - v).z = u.z - v.z := rfl

@[simp] def neg (u : Vec3 R) : Vec3 R := ⟨-u.x, -u.y, -u.z⟩
instance instNegVec3 : Neg (Vec3 R) := ⟨neg⟩

@[simp] lemma neg_x (u : Vec3 R) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : Vec3 R) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : Vec3 R) : (-u).z = -u.z := rfl

@[simp] def smulLeft (a : R) (u : Vec3 R) : Vec3 R := ⟨a * u.x, a * u.y, a * u.z⟩
@[simp] def smulRight (u : Vec3 R) (a : R) : Vec3 R := ⟨u.x * a, u.y * a, u.z * a⟩

@[simp] def dot (u v : Vec3 R) : R := u.x * v.x + u.y * v.y + u.z * v.z

@[simp] def cross (u v : Vec3 R) : Vec3 R :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

@[simp] def nambu3 (u : Vec3 R) : R :=
  u.x * u.y * u.z - u.x * u.z * u.y +
  u.y * u.z * u.x - u.y * u.x * u.z +
  u.z * u.x * u.y - u.z * u.y * u.x

@[simp] def baryonDet3 (u₁ u₂ u₃ : Vec3 R) : R := dot (cross u₁ u₂) u₃

end Vec3

/-- A 4-component twistor `Z = (w, x, y, z) ∈ R⁴` (projective index `0 = w`). -/
@[ext]
structure Twistor4 (R : Type*) where
  w : R
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Twistor4
variable {R : Type*} [Ring R]

@[simp] def spatialVec (Z : Twistor4 R) : Vec3 R := ⟨Z.x, Z.y, Z.z⟩

@[simp] def origin : Twistor4 R := ⟨1, 0, 0, 0⟩

@[simp] def affineTwistor (u : Vec3 R) : Twistor4 R := ⟨1, u.x, u.y, u.z⟩

@[simp] def pluckerU (ZA ZB : Twistor4 R) : Vec3 R :=
  ⟨ZA.w * ZB.x - ZA.x * ZB.w,
   ZA.w * ZB.y - ZA.y * ZB.w,
   ZA.w * ZB.z - ZA.z * ZB.w⟩

@[simp] def pluckerV (ZA ZB : Twistor4 R) : Vec3 R := Vec3.cross (spatialVec ZA) (spatialVec ZB)

end Twistor4

open Twistor4

/-- Zorn `2 × 2` split-octonion vector-matrix `[[a, u], [v, d]]` over a ring `R`. -/
@[ext]
structure ZornMatrix (R : Type*) where
  a : R
  u : Vec3 R
  v : Vec3 R
  d : R
  deriving DecidableEq, Repr, Inhabited

namespace ZornMatrix
variable {R : Type*} [Ring R]

@[simp] def zero : ZornMatrix R := ⟨0, 0, 0, 0⟩
instance instZeroZornMatrix : Zero (ZornMatrix R) := ⟨zero⟩

@[simp] lemma zero_a : (0 : ZornMatrix R).a = 0 := rfl
@[simp] lemma zero_u : (0 : ZornMatrix R).u = 0 := rfl
@[simp] lemma zero_v : (0 : ZornMatrix R).v = 0 := rfl
@[simp] lemma zero_d : (0 : ZornMatrix R).d = 0 := rfl

@[simp] def one : ZornMatrix R := ⟨1, 0, 0, 1⟩
instance instOneZornMatrix : One (ZornMatrix R) := ⟨one⟩

@[simp] lemma one_a : (1 : ZornMatrix R).a = 1 := rfl
@[simp] lemma one_u : (1 : ZornMatrix R).u = 0 := rfl
@[simp] lemma one_v : (1 : ZornMatrix R).v = 0 := rfl
@[simp] lemma one_d : (1 : ZornMatrix R).d = 1 := rfl

@[simp] def add (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a + Y.a, X.u + Y.u, X.v + Y.v, X.d + Y.d⟩
instance instAddZornMatrix : Add (ZornMatrix R) := ⟨add⟩

@[simp] lemma add_a (X Y : ZornMatrix R) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma add_u (X Y : ZornMatrix R) : (X + Y).u = X.u + Y.u := rfl
@[simp] lemma add_v (X Y : ZornMatrix R) : (X + Y).v = X.v + Y.v := rfl
@[simp] lemma add_d (X Y : ZornMatrix R) : (X + Y).d = X.d + Y.d := rfl

@[simp] def sub (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a - Y.a, X.u - Y.u, X.v - Y.v, X.d - Y.d⟩
instance instSubZornMatrix : Sub (ZornMatrix R) := ⟨sub⟩

@[simp] lemma sub_a (X Y : ZornMatrix R) : (X - Y).a = X.a - Y.a := rfl
@[simp] lemma sub_u (X Y : ZornMatrix R) : (X - Y).u = X.u - Y.u := rfl
@[simp] lemma sub_v (X Y : ZornMatrix R) : (X - Y).v = X.v - Y.v := rfl
@[simp] lemma sub_d (X Y : ZornMatrix R) : (X - Y).d = X.d - Y.d := rfl

@[simp] def neg (X : ZornMatrix R) : ZornMatrix R := ⟨-X.a, -X.u, -X.v, -X.d⟩
instance instNegZornMatrix : Neg (ZornMatrix R) := ⟨neg⟩

@[simp] def smul (c : R) (X : ZornMatrix R) : ZornMatrix R :=
  ⟨c * X.a, Vec3.smulLeft c X.u, Vec3.smulLeft c X.v, c * X.d⟩

@[simp] def mul (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨ X.a * Y.a + Vec3.dot X.u Y.v,
    Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d - Vec3.cross X.v Y.v,
    Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v + Vec3.cross X.u Y.u,
    Vec3.dot X.v Y.u + X.d * Y.d ⟩
instance instMulZornMatrix : Mul (ZornMatrix R) := ⟨mul⟩

@[simp] lemma mul_a (X Y : ZornMatrix R) : (X * Y).a = X.a * Y.a + Vec3.dot X.u Y.v := rfl
@[simp] lemma mul_u (X Y : ZornMatrix R) :
    (X * Y).u = Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d - Vec3.cross X.v Y.v := rfl
@[simp] lemma mul_v (X Y : ZornMatrix R) :
    (X * Y).v = Vec3.smulRight X.v Y.a + Vec3.smulLeft X.d Y.v + Vec3.cross X.u Y.u := rfl
@[simp] lemma mul_d (X Y : ZornMatrix R) : (X * Y).d = Vec3.dot X.v Y.u + X.d * Y.d := rfl

@[simp] def zornConePlus (u : Vec3 R) : ZornMatrix R := ⟨0, u, 0, 0⟩
@[simp] def zornConeMinus (v : Vec3 R) : ZornMatrix R := ⟨0, 0, v, 0⟩
@[simp] def zornPhi (u v : Vec3 R) : ZornMatrix R := ⟨0, u, v, 0⟩
@[simp] def gamma5 : ZornMatrix R := ⟨1, 0, 0, -1⟩

@[simp] def associator (X Y Z : ZornMatrix R) : ZornMatrix R := (X * Y) * Z - X * (Y * Z)

end ZornMatrix

open ZornMatrix

/-- `4 × 4` matrix over `R`, used for Plücker bivectors and twistor determinants. -/
@[ext]
structure Mat4 (R : Type*) where
  m00 : R
  m01 : R
  m02 : R
  m03 : R
  m10 : R
  m11 : R
  m12 : R
  m13 : R
  m20 : R
  m21 : R
  m22 : R
  m23 : R
  m30 : R
  m31 : R
  m32 : R
  m33 : R
  deriving DecidableEq, Repr, Inhabited

namespace Mat4
variable {R : Type*} [Ring R]

@[simp] def zero : Mat4 R := ⟨0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩
instance instZeroMat4 : Zero (Mat4 R) := ⟨zero⟩

@[simp] def one : Mat4 R := ⟨1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1⟩
instance instOneMat4 : One (Mat4 R) := ⟨one⟩

@[simp] lemma one_def : (1 : Mat4 R) = one := rfl

@[simp] def add (A B : Mat4 R) : Mat4 R :=
  ⟨A.m00 + B.m00, A.m01 + B.m01, A.m02 + B.m02, A.m03 + B.m03,
   A.m10 + B.m10, A.m11 + B.m11, A.m12 + B.m12, A.m13 + B.m13,
   A.m20 + B.m20, A.m21 + B.m21, A.m22 + B.m22, A.m23 + B.m23,
   A.m30 + B.m30, A.m31 + B.m31, A.m32 + B.m32, A.m33 + B.m33⟩
instance instAddMat4 : Add (Mat4 R) := ⟨add⟩

@[simp] def neg (A : Mat4 R) : Mat4 R :=
  ⟨-A.m00, -A.m01, -A.m02, -A.m03,
   -A.m10, -A.m11, -A.m12, -A.m13,
   -A.m20, -A.m21, -A.m22, -A.m23,
   -A.m30, -A.m31, -A.m32, -A.m33⟩
instance instNegMat4 : Neg (Mat4 R) := ⟨neg⟩

@[simp] lemma neg_def (A : Mat4 R) : -A = neg A := rfl

@[simp] def sub (A B : Mat4 R) : Mat4 R :=
  ⟨A.m00 - B.m00, A.m01 - B.m01, A.m02 - B.m02, A.m03 - B.m03,
   A.m10 - B.m10, A.m11 - B.m11, A.m12 - B.m12, A.m13 - B.m13,
   A.m20 - B.m20, A.m21 - B.m21, A.m22 - B.m22, A.m23 - B.m23,
   A.m30 - B.m30, A.m31 - B.m31, A.m32 - B.m32, A.m33 - B.m33⟩
instance instSubMat4 : Sub (Mat4 R) := ⟨sub⟩

@[simp] def smul (c : R) (A : Mat4 R) : Mat4 R :=
  ⟨c * A.m00, c * A.m01, c * A.m02, c * A.m03,
   c * A.m10, c * A.m11, c * A.m12, c * A.m13,
   c * A.m20, c * A.m21, c * A.m22, c * A.m23,
   c * A.m30, c * A.m31, c * A.m32, c * A.m33⟩

@[simp] def mul (A B : Mat4 R) : Mat4 R :=
  ⟨ A.m00 * B.m00 + A.m01 * B.m10 + A.m02 * B.m20 + A.m03 * B.m30,
    A.m00 * B.m01 + A.m01 * B.m11 + A.m02 * B.m21 + A.m03 * B.m31,
    A.m00 * B.m02 + A.m01 * B.m12 + A.m02 * B.m22 + A.m03 * B.m32,
    A.m00 * B.m03 + A.m01 * B.m13 + A.m02 * B.m23 + A.m03 * B.m33,

    A.m10 * B.m00 + A.m11 * B.m10 + A.m12 * B.m20 + A.m13 * B.m30,
    A.m10 * B.m01 + A.m11 * B.m11 + A.m12 * B.m21 + A.m13 * B.m31,
    A.m10 * B.m02 + A.m11 * B.m12 + A.m12 * B.m22 + A.m13 * B.m32,
    A.m10 * B.m03 + A.m11 * B.m13 + A.m12 * B.m23 + A.m13 * B.m33,

    A.m20 * B.m00 + A.m21 * B.m10 + A.m22 * B.m20 + A.m23 * B.m30,
    A.m20 * B.m01 + A.m21 * B.m11 + A.m22 * B.m21 + A.m23 * B.m31,
    A.m20 * B.m02 + A.m21 * B.m12 + A.m22 * B.m22 + A.m23 * B.m32,
    A.m20 * B.m03 + A.m21 * B.m13 + A.m22 * B.m23 + A.m23 * B.m33,

    A.m30 * B.m00 + A.m31 * B.m10 + A.m32 * B.m20 + A.m33 * B.m30,
    A.m30 * B.m01 + A.m31 * B.m11 + A.m32 * B.m21 + A.m33 * B.m31,
    A.m30 * B.m02 + A.m31 * B.m12 + A.m32 * B.m22 + A.m33 * B.m32,
    A.m30 * B.m03 + A.m31 * B.m13 + A.m32 * B.m23 + A.m33 * B.m33 ⟩
instance instMulMat4 : Mul (Mat4 R) := ⟨mul⟩

@[simp] lemma mul_def (A B : Mat4 R) : A * B = mul A B := rfl

end Mat4

open Mat4

section Definitions
variable {R : Type*} [Ring R]

/-- `4 × 4` skew-symmetric Plücker bivector matrix `P₄(u, v) ∈ Mat4 R`. -/
@[simp] def pluckerMat4 (u v : Vec3 R) : Mat4 R :=
  ⟨0,    u.x,  u.y,  u.z,
   -u.x, 0,    v.z, -v.y,
   -u.y, -v.z, 0,    v.x,
   -u.z, v.y, -v.x, 0   ⟩

/-- Hodge dual `4 × 4` Plücker matrix `⋆P₄(u, v) = P₄(v, u)`. -/
@[simp] def pluckerHodge4 (u v : Vec3 R) : Mat4 R :=
  pluckerMat4 v u

/-- Assemble four 4-twistors as the rows of a `4 × 4` matrix. -/
@[simp] def ofTwistors (Z0 Z1 Z2 Z3 : Twistor4 R) : Mat4 R :=
  ⟨Z0.w, Z0.x, Z0.y, Z0.z,
   Z1.w, Z1.x, Z1.y, Z1.z,
   Z2.w, Z2.x, Z2.y, Z2.z,
   Z3.w, Z3.x, Z3.y, Z3.z⟩

/-- Explicit `4 × 4` determinant. -/
@[simp] def det4 (M : Mat4 R) : R :=
  M.m00 * (M.m11 * (M.m22 * M.m33 - M.m23 * M.m32) - M.m12 * (M.m21 * M.m33 - M.m23 * M.m31) + M.m13 * (M.m21 * M.m32 - M.m22 * M.m31)) -
  M.m01 * (M.m10 * (M.m22 * M.m33 - M.m23 * M.m32) - M.m12 * (M.m20 * M.m33 - M.m23 * M.m30) + M.m13 * (M.m20 * M.m32 - M.m22 * M.m30)) +
  M.m02 * (M.m10 * (M.m21 * M.m33 - M.m23 * M.m31) - M.m11 * (M.m20 * M.m33 - M.m23 * M.m30) + M.m13 * (M.m20 * M.m31 - M.m21 * M.m30)) -
  M.m03 * (M.m10 * (M.m21 * M.m32 - M.m22 * M.m31) - M.m11 * (M.m20 * M.m32 - M.m22 * M.m30) + M.m12 * (M.m20 * M.m31 - M.m21 * M.m30))

/-- Amplituhedron 4-bracket `⟨Z₀ Z₁ Z₂ Z₃⟩` via `det4 (ofTwistors Z₀ Z₁ Z₂ Z₃)`. -/
@[simp] def twistorBracket4 (Z0 Z1 Z2 Z3 : Twistor4 R) : R :=
  det4 (ofTwistors Z0 Z1 Z2 Z3)

/-- Embed Plücker coordinates into `ZornMatrix R`. -/
@[simp] def zornPlucker (ZA ZB : Twistor4 R) : ZornMatrix R :=
  zornPhi (Twistor4.pluckerU ZA ZB) (Twistor4.pluckerV ZA ZB)

end Definitions

section NonCommutativeRing
variable {R : Type*} [Ring R]

/-- **Theorem XVIII.1 (`noncommutative_mat4_plucker_hodge_and_nambu_klein_anomaly`)**:
Over any non-commutative associative ring `[Ring R]`:
1. In the full `4 × 4` matrix product `M_PH = -(pluckerMat4 u v * pluckerHodge4 u v)`:
   - the `(0,0)` entry `M_PH.m00` is the scalar condensate `u · v`,
   - the first row `⟨M_PH.m01, M_PH.m02, M_PH.m03⟩` is the upper self-wedge anomaly `u × u`,
   - the first column `⟨M_PH.m10, M_PH.m20, M_PH.m30⟩` is the negated lower self-wedge anomaly `-(v × v)`.
2. The self-Plücker Klein quadric anomaly `u · (u × u)` equals the Nambu 3-bracket `Vec3.nambu3 u`,
   which coincides with the diagonal of the cubic Zorn self-associator
   `associator (zornConePlus u) (zornConePlus u) (zornConePlus u)`. -/
theorem noncommutative_mat4_plucker_hodge_and_nambu_klein_anomaly (u v : Vec3 R) :
    let M_PH := -(pluckerMat4 u v * pluckerHodge4 u v)
    M_PH.m00 = Vec3.dot u v ∧
    (⟨M_PH.m01, M_PH.m02, M_PH.m03⟩ : Vec3 R) = Vec3.cross u u ∧
    (⟨M_PH.m10, M_PH.m20, M_PH.m30⟩ : Vec3 R) = -Vec3.cross v v ∧
    Vec3.dot u (Vec3.cross u u) = Vec3.nambu3 u ∧
    associator (zornConePlus u) (zornConePlus u) (zornConePlus u) =
      ⟨-Vec3.nambu3 u, 0, 0, Vec3.nambu3 u⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [pluckerHodge4, pluckerMat4, Mat4.mul_def, Mat4.mul,
      Mat4.neg_def, Mat4.neg, Vec3.dot]
    noncomm_ring
  · ext <;>
    · simp only [pluckerHodge4, pluckerMat4, Mat4.mul_def, Mat4.mul,
        Mat4.neg_def, Mat4.neg, Vec3.cross]
      noncomm_ring
  · ext <;>
    · simp only [pluckerHodge4, pluckerMat4, Mat4.mul_def, Mat4.mul,
        Mat4.neg_def, Mat4.neg, Vec3.cross, Vec3.neg_x, Vec3.neg_y, Vec3.neg_z]
      noncomm_ring
  · simp only [Vec3.dot, Vec3.cross, Vec3.nambu3]
    noncomm_ring
  · ext <;>
    · simp only [associator, zornConePlus, ZornMatrix.mul_a, ZornMatrix.mul_u,
        ZornMatrix.mul_v, ZornMatrix.mul_d, ZornMatrix.sub_a, ZornMatrix.sub_u,
        ZornMatrix.sub_v, ZornMatrix.sub_d, Vec3.dot, Vec3.cross,
        Vec3.smulLeft, Vec3.smulRight, Vec3.nambu3,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      try noncomm_ring

/-- **Trap T16 Witness (`zornConePlus_mul_zornConeMinus_ne_comm`)**:
Over any nontrivial ring `[Ring R] [Nontrivial R]`, `ZornMatrix R` is strictly non-commutative. -/
theorem zornConePlus_mul_zornConeMinus_ne_comm [Nontrivial R] :
    zornConePlus (⟨1, 0, 0⟩ : Vec3 R) * zornConeMinus ⟨1, 0, 0⟩ ≠
      zornConeMinus (⟨1, 0, 0⟩ : Vec3 R) * zornConePlus ⟨1, 0, 0⟩ := by
  intro h
  have ha : (zornConePlus (⟨1, 0, 0⟩ : Vec3 R) * zornConeMinus ⟨1, 0, 0⟩).a =
      (zornConeMinus (⟨1, 0, 0⟩ : Vec3 R) * zornConePlus ⟨1, 0, 0⟩).a := by
    rw [h]
  simp at ha

end NonCommutativeRing

section CommutativeTwistorGrassmannian
variable {K : Type*} [CommRing K]

/-- **Theorem XVIII.2 (`klein_quadric_and_zorn_nilpotency_of_twistor_lines`)**:
Over any commutative ring `[CommRing K]`:
1. `-(pluckerMat4 u v * pluckerHodge4 u v) = Mat4.smul (Vec3.dot u v) (1 : Mat4 K)`,
2. `zornPhi u v * zornPhi u v = ZornMatrix.smul (Vec3.dot u v) (1 : ZornMatrix K)`,
3. The Plücker–Klein quadric identity `Vec3.dot (pluckerU ZA ZB) (pluckerV ZA ZB) = 0` holds,
4. Every simple twistor line `zornPlucker ZA ZB` is square-zero nilpotent in `ZornMatrix K`. -/
theorem klein_quadric_and_zorn_nilpotency_of_twistor_lines
    (u v : Vec3 K) (ZA ZB : Twistor4 K) :
    -(pluckerMat4 u v * pluckerHodge4 u v) =
      Mat4.smul (Vec3.dot u v) (1 : Mat4 K) ∧
    zornPhi u v * zornPhi u v =
      ZornMatrix.smul (Vec3.dot u v) (1 : ZornMatrix K) ∧
    Vec3.dot (pluckerU ZA ZB) (pluckerV ZA ZB) = 0 ∧
    zornPlucker ZA ZB * zornPlucker ZA ZB = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext <;>
    · simp only [pluckerHodge4, pluckerMat4, Mat4.smul,
        Mat4.mul_def, Mat4.mul, Mat4.neg_def, Mat4.neg, Mat4.one_def, Mat4.one, Vec3.dot]
      ring
  · ext <;>
    · simp only [zornPhi, ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u,
        ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · dsimp [Twistor4.pluckerU, Twistor4.pluckerV, Twistor4.spatialVec,
      Vec3.dot, Vec3.cross]
    ring
  · ext <;>
    · simp only [zornPlucker, zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
        Twistor4.spatialVec,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        ZornMatrix.zero_a, ZornMatrix.zero_u, ZornMatrix.zero_v, ZornMatrix.zero_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring

/-- **Theorem XVIII.3 (`amplituhedron_4bracket_eq_zorn_plucker_anticommutator_and_baryon`)**:
Over any commutative ring `[CommRing K]`:
1. The Zorn anticommutator of two twistor lines equals `⟨Z₀ Z₁ Z₂ Z₃⟩ I₂`,
2. The dual Plücker 3-vector `v(Q₁, Q₂)` is the Zorn diquark product `N_+(u₁) · N_+(u₂)`,
3. The origin-anchored 4-bracket equals the 3-quark baryon determinant `Vec3.baryonDet3 u₁ u₂ u₃`,
4. The anticommutator of `N_+(u₁) · N_+(u₂)` with `N_+(u₃)` equals `⟨origin Q₁ Q₂ Q₃⟩ I₂`,
5. The affine 4-bracket equals the relative-chord baryon determinant,
6. The affine 4-bracket equals the 4-facet cyclic boundary sum of baryons. -/
theorem amplituhedron_4bracket_eq_zorn_plucker_anticommutator_and_baryon
    (Z0 Z1 Z2 Z3 : Twistor4 K) (z10 z20 z30 : K) (u0 u1 u2 u3 : Vec3 K) :
    let Q1 : Twistor4 K := ⟨z10, u1.x, u1.y, u1.z⟩
    let Q2 : Twistor4 K := ⟨z20, u2.x, u2.y, u2.z⟩
    let Q3 : Twistor4 K := ⟨z30, u3.x, u3.y, u3.z⟩
    zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1 =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    zornConeMinus (pluckerV Q1 Q2) = zornConePlus u1 * zornConePlus u2 ∧
    twistorBracket4 Twistor4.origin Q1 Q2 Q3 = Vec3.baryonDet3 u1 u2 u3 ∧
    (zornConePlus u1 * zornConePlus u2) * zornConePlus u3 +
      zornConePlus u3 * (zornConePlus u1 * zornConePlus u2) =
      ZornMatrix.smul (twistorBracket4 Twistor4.origin Q1 Q2 Q3) (1 : ZornMatrix K) ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0) ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 u1 u2 u3 - Vec3.baryonDet3 u0 u2 u3 +
      Vec3.baryonDet3 u0 u1 u3 - Vec3.baryonDet3 u0 u1 u2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    · simp only [zornPlucker, zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
        Twistor4.spatialVec, twistorBracket4, det4, ofTwistors,
        ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u, ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [zornConeMinus, zornConePlus, Twistor4.pluckerV, Twistor4.spatialVec,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · simp only [twistorBracket4, det4, ofTwistors, Twistor4.origin, Vec3.baryonDet3,
      Vec3.dot, Vec3.cross]
    ring
  · ext <;>
    · simp only [zornConePlus, twistorBracket4, det4, ofTwistors, Twistor4.origin,
        ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u, ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · simp only [twistorBracket4, det4, ofTwistors, Twistor4.affineTwistor,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
    ring
  · simp only [twistorBracket4, det4, ofTwistors, Twistor4.affineTwistor,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross]
    ring

end CommutativeTwistorGrassmannian

end InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
