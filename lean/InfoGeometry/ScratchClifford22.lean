/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

namespace ScratchClifford22

universe u
variable {R : Type u} [CommRing R]

@[ext]
structure Mat4 (R : Type u) where
  a00 : R
  a01 : R
  a02 : R
  a03 : R
  a10 : R
  a11 : R
  a12 : R
  a13 : R
  a20 : R
  a21 : R
  a22 : R
  a23 : R
  a30 : R
  a31 : R
  a32 : R
  a33 : R

namespace Mat4

def zero : Mat4 R := ⟨0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩
def one : Mat4 R := ⟨1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1⟩

def add (X Y : Mat4 R) : Mat4 R :=
  ⟨X.a00+Y.a00, X.a01+Y.a01, X.a02+Y.a02, X.a03+Y.a03,
   X.a10+Y.a10, X.a11+Y.a11, X.a12+Y.a12, X.a13+Y.a13,
   X.a20+Y.a20, X.a21+Y.a21, X.a22+Y.a22, X.a23+Y.a23,
   X.a30+Y.a30, X.a31+Y.a31, X.a32+Y.a32, X.a33+Y.a33⟩

def sub (X Y : Mat4 R) : Mat4 R :=
  ⟨X.a00-Y.a00, X.a01-Y.a01, X.a02-Y.a02, X.a03-Y.a03,
   X.a10-Y.a10, X.a11-Y.a11, X.a12-Y.a12, X.a13-Y.a13,
   X.a20-Y.a20, X.a21-Y.a21, X.a22-Y.a22, X.a23-Y.a23,
   X.a30-Y.a30, X.a31-Y.a31, X.a32-Y.a32, X.a33-Y.a33⟩

def neg (X : Mat4 R) : Mat4 R :=
  ⟨-X.a00, -X.a01, -X.a02, -X.a03,
   -X.a10, -X.a11, -X.a12, -X.a13,
   -X.a20, -X.a21, -X.a22, -X.a23,
   -X.a30, -X.a31, -X.a32, -X.a33⟩

def mul (X Y : Mat4 R) : Mat4 R :=
  ⟨X.a00*Y.a00 + X.a01*Y.a10 + X.a02*Y.a20 + X.a03*Y.a30,
   X.a00*Y.a01 + X.a01*Y.a11 + X.a02*Y.a21 + X.a03*Y.a31,
   X.a00*Y.a02 + X.a01*Y.a12 + X.a02*Y.a22 + X.a03*Y.a32,
   X.a00*Y.a03 + X.a01*Y.a13 + X.a02*Y.a23 + X.a03*Y.a33,

   X.a10*Y.a00 + X.a11*Y.a10 + X.a12*Y.a20 + X.a13*Y.a30,
   X.a10*Y.a01 + X.a11*Y.a11 + X.a12*Y.a21 + X.a13*Y.a31,
   X.a10*Y.a02 + X.a11*Y.a12 + X.a12*Y.a22 + X.a13*Y.a32,
   X.a10*Y.a03 + X.a11*Y.a13 + X.a12*Y.a23 + X.a13*Y.a33,

   X.a20*Y.a00 + X.a21*Y.a10 + X.a22*Y.a20 + X.a23*Y.a30,
   X.a20*Y.a01 + X.a21*Y.a11 + X.a22*Y.a21 + X.a23*Y.a31,
   X.a20*Y.a02 + X.a21*Y.a12 + X.a22*Y.a22 + X.a23*Y.a32,
   X.a20*Y.a03 + X.a21*Y.a13 + X.a22*Y.a23 + X.a23*Y.a33,

   X.a30*Y.a00 + X.a31*Y.a10 + X.a32*Y.a20 + X.a33*Y.a30,
   X.a30*Y.a01 + X.a31*Y.a11 + X.a32*Y.a21 + X.a33*Y.a31,
   X.a30*Y.a02 + X.a31*Y.a12 + X.a32*Y.a22 + X.a33*Y.a32,
   X.a30*Y.a03 + X.a31*Y.a13 + X.a32*Y.a23 + X.a33*Y.a33⟩

instance : Zero (Mat4 R) := ⟨zero⟩
instance : One (Mat4 R) := ⟨one⟩
instance : Add (Mat4 R) := ⟨add⟩
instance : Sub (Mat4 R) := ⟨sub⟩
instance : Neg (Mat4 R) := ⟨neg⟩
instance : Mul (Mat4 R) := ⟨mul⟩

@[simp] lemma mul_a00 (X Y : Mat4 R) :
    (X * Y).a00 = X.a00*Y.a00 + X.a01*Y.a10 + X.a02*Y.a20 + X.a03*Y.a30 := rfl

@[simp] lemma mul_a01 (X Y : Mat4 R) :
    (X * Y).a01 = X.a00*Y.a01 + X.a01*Y.a11 + X.a02*Y.a21 + X.a03*Y.a31 := rfl

@[simp] lemma mul_a02 (X Y : Mat4 R) :
    (X * Y).a02 = X.a00*Y.a02 + X.a01*Y.a12 + X.a02*Y.a22 + X.a03*Y.a32 := rfl

@[simp] lemma mul_a03 (X Y : Mat4 R) :
    (X * Y).a03 = X.a00*Y.a03 + X.a01*Y.a13 + X.a02*Y.a23 + X.a03*Y.a33 := rfl

@[simp] lemma mul_a10 (X Y : Mat4 R) :
    (X * Y).a10 = X.a10*Y.a00 + X.a11*Y.a10 + X.a12*Y.a20 + X.a13*Y.a30 := rfl

@[simp] lemma mul_a11 (X Y : Mat4 R) :
    (X * Y).a11 = X.a10*Y.a01 + X.a11*Y.a11 + X.a12*Y.a21 + X.a13*Y.a31 := rfl

@[simp] lemma mul_a12 (X Y : Mat4 R) :
    (X * Y).a12 = X.a10*Y.a02 + X.a11*Y.a12 + X.a12*Y.a22 + X.a13*Y.a32 := rfl

@[simp] lemma mul_a13 (X Y : Mat4 R) :
    (X * Y).a13 = X.a10*Y.a03 + X.a11*Y.a13 + X.a12*Y.a23 + X.a13*Y.a33 := rfl

@[simp] lemma mul_a20 (X Y : Mat4 R) :
    (X * Y).a20 = X.a20*Y.a00 + X.a21*Y.a10 + X.a22*Y.a20 + X.a23*Y.a30 := rfl

@[simp] lemma mul_a21 (X Y : Mat4 R) :
    (X * Y).a21 = X.a20*Y.a01 + X.a21*Y.a11 + X.a22*Y.a21 + X.a23*Y.a31 := rfl

@[simp] lemma mul_a22 (X Y : Mat4 R) :
    (X * Y).a22 = X.a20*Y.a02 + X.a21*Y.a12 + X.a22*Y.a22 + X.a23*Y.a32 := rfl

@[simp] lemma mul_a23 (X Y : Mat4 R) :
    (X * Y).a23 = X.a20*Y.a03 + X.a21*Y.a13 + X.a22*Y.a23 + X.a23*Y.a33 := rfl

@[simp] lemma mul_a30 (X Y : Mat4 R) :
    (X * Y).a30 = X.a30*Y.a00 + X.a31*Y.a10 + X.a32*Y.a20 + X.a33*Y.a30 := rfl

@[simp] lemma mul_a31 (X Y : Mat4 R) :
    (X * Y).a31 = X.a30*Y.a01 + X.a31*Y.a11 + X.a32*Y.a21 + X.a33*Y.a31 := rfl

@[simp] lemma mul_a32 (X Y : Mat4 R) :
    (X * Y).a32 = X.a30*Y.a02 + X.a31*Y.a12 + X.a32*Y.a22 + X.a33*Y.a32 := rfl

@[simp] lemma mul_a33 (X Y : Mat4 R) :
    (X * Y).a33 = X.a30*Y.a03 + X.a31*Y.a13 + X.a32*Y.a23 + X.a33*Y.a33 := rfl

@[simp] lemma add_a00 (X Y : Mat4 R) :
    (X + Y).a00 = X.a00 + Y.a00 := rfl

@[simp] lemma add_a01 (X Y : Mat4 R) :
    (X + Y).a01 = X.a01 + Y.a01 := rfl

@[simp] lemma add_a02 (X Y : Mat4 R) :
    (X + Y).a02 = X.a02 + Y.a02 := rfl

@[simp] lemma add_a03 (X Y : Mat4 R) :
    (X + Y).a03 = X.a03 + Y.a03 := rfl

@[simp] lemma add_a10 (X Y : Mat4 R) :
    (X + Y).a10 = X.a10 + Y.a10 := rfl

@[simp] lemma add_a11 (X Y : Mat4 R) :
    (X + Y).a11 = X.a11 + Y.a11 := rfl

@[simp] lemma add_a12 (X Y : Mat4 R) :
    (X + Y).a12 = X.a12 + Y.a12 := rfl

@[simp] lemma add_a13 (X Y : Mat4 R) :
    (X + Y).a13 = X.a13 + Y.a13 := rfl

@[simp] lemma add_a20 (X Y : Mat4 R) :
    (X + Y).a20 = X.a20 + Y.a20 := rfl

@[simp] lemma add_a21 (X Y : Mat4 R) :
    (X + Y).a21 = X.a21 + Y.a21 := rfl

@[simp] lemma add_a22 (X Y : Mat4 R) :
    (X + Y).a22 = X.a22 + Y.a22 := rfl

@[simp] lemma add_a23 (X Y : Mat4 R) :
    (X + Y).a23 = X.a23 + Y.a23 := rfl

@[simp] lemma add_a30 (X Y : Mat4 R) :
    (X + Y).a30 = X.a30 + Y.a30 := rfl

@[simp] lemma add_a31 (X Y : Mat4 R) :
    (X + Y).a31 = X.a31 + Y.a31 := rfl

@[simp] lemma add_a32 (X Y : Mat4 R) :
    (X + Y).a32 = X.a32 + Y.a32 := rfl

@[simp] lemma add_a33 (X Y : Mat4 R) :
    (X + Y).a33 = X.a33 + Y.a33 := rfl

@[simp] lemma sub_a00 (X Y : Mat4 R) :
    (X - Y).a00 = X.a00 - Y.a00 := rfl

@[simp] lemma sub_a01 (X Y : Mat4 R) :
    (X - Y).a01 = X.a01 - Y.a01 := rfl

@[simp] lemma sub_a02 (X Y : Mat4 R) :
    (X - Y).a02 = X.a02 - Y.a02 := rfl

@[simp] lemma sub_a03 (X Y : Mat4 R) :
    (X - Y).a03 = X.a03 - Y.a03 := rfl

@[simp] lemma sub_a10 (X Y : Mat4 R) :
    (X - Y).a10 = X.a10 - Y.a10 := rfl

@[simp] lemma sub_a11 (X Y : Mat4 R) :
    (X - Y).a11 = X.a11 - Y.a11 := rfl

@[simp] lemma sub_a12 (X Y : Mat4 R) :
    (X - Y).a12 = X.a12 - Y.a12 := rfl

@[simp] lemma sub_a13 (X Y : Mat4 R) :
    (X - Y).a13 = X.a13 - Y.a13 := rfl

@[simp] lemma sub_a20 (X Y : Mat4 R) :
    (X - Y).a20 = X.a20 - Y.a20 := rfl

@[simp] lemma sub_a21 (X Y : Mat4 R) :
    (X - Y).a21 = X.a21 - Y.a21 := rfl

@[simp] lemma sub_a22 (X Y : Mat4 R) :
    (X - Y).a22 = X.a22 - Y.a22 := rfl

@[simp] lemma sub_a23 (X Y : Mat4 R) :
    (X - Y).a23 = X.a23 - Y.a23 := rfl

@[simp] lemma sub_a30 (X Y : Mat4 R) :
    (X - Y).a30 = X.a30 - Y.a30 := rfl

@[simp] lemma sub_a31 (X Y : Mat4 R) :
    (X - Y).a31 = X.a31 - Y.a31 := rfl

@[simp] lemma sub_a32 (X Y : Mat4 R) :
    (X - Y).a32 = X.a32 - Y.a32 := rfl

@[simp] lemma sub_a33 (X Y : Mat4 R) :
    (X - Y).a33 = X.a33 - Y.a33 := rfl

@[simp] lemma neg_a00 (X : Mat4 R) :
    (-X).a00 = -X.a00 := rfl

@[simp] lemma neg_a01 (X : Mat4 R) :
    (-X).a01 = -X.a01 := rfl

@[simp] lemma neg_a02 (X : Mat4 R) :
    (-X).a02 = -X.a02 := rfl

@[simp] lemma neg_a03 (X : Mat4 R) :
    (-X).a03 = -X.a03 := rfl

@[simp] lemma neg_a10 (X : Mat4 R) :
    (-X).a10 = -X.a10 := rfl

@[simp] lemma neg_a11 (X : Mat4 R) :
    (-X).a11 = -X.a11 := rfl

@[simp] lemma neg_a12 (X : Mat4 R) :
    (-X).a12 = -X.a12 := rfl

@[simp] lemma neg_a13 (X : Mat4 R) :
    (-X).a13 = -X.a13 := rfl

@[simp] lemma neg_a20 (X : Mat4 R) :
    (-X).a20 = -X.a20 := rfl

@[simp] lemma neg_a21 (X : Mat4 R) :
    (-X).a21 = -X.a21 := rfl

@[simp] lemma neg_a22 (X : Mat4 R) :
    (-X).a22 = -X.a22 := rfl

@[simp] lemma neg_a23 (X : Mat4 R) :
    (-X).a23 = -X.a23 := rfl

@[simp] lemma neg_a30 (X : Mat4 R) :
    (-X).a30 = -X.a30 := rfl

@[simp] lemma neg_a31 (X : Mat4 R) :
    (-X).a31 = -X.a31 := rfl

@[simp] lemma neg_a32 (X : Mat4 R) :
    (-X).a32 = -X.a32 := rfl

@[simp] lemma neg_a33 (X : Mat4 R) :
    (-X).a33 = -X.a33 := rfl

@[simp] lemma zero_a00 :
    (0 : Mat4 R).a00 = 0 := rfl

@[simp] lemma zero_a01 :
    (0 : Mat4 R).a01 = 0 := rfl

@[simp] lemma zero_a02 :
    (0 : Mat4 R).a02 = 0 := rfl

@[simp] lemma zero_a03 :
    (0 : Mat4 R).a03 = 0 := rfl

@[simp] lemma zero_a10 :
    (0 : Mat4 R).a10 = 0 := rfl

@[simp] lemma zero_a11 :
    (0 : Mat4 R).a11 = 0 := rfl

@[simp] lemma zero_a12 :
    (0 : Mat4 R).a12 = 0 := rfl

@[simp] lemma zero_a13 :
    (0 : Mat4 R).a13 = 0 := rfl

@[simp] lemma zero_a20 :
    (0 : Mat4 R).a20 = 0 := rfl

@[simp] lemma zero_a21 :
    (0 : Mat4 R).a21 = 0 := rfl

@[simp] lemma zero_a22 :
    (0 : Mat4 R).a22 = 0 := rfl

@[simp] lemma zero_a23 :
    (0 : Mat4 R).a23 = 0 := rfl

@[simp] lemma zero_a30 :
    (0 : Mat4 R).a30 = 0 := rfl

@[simp] lemma zero_a31 :
    (0 : Mat4 R).a31 = 0 := rfl

@[simp] lemma zero_a32 :
    (0 : Mat4 R).a32 = 0 := rfl

@[simp] lemma zero_a33 :
    (0 : Mat4 R).a33 = 0 := rfl

def smul (c : R) (X : Mat4 R) : Mat4 R :=
  ⟨c*X.a00, c*X.a01, c*X.a02, c*X.a03,
   c*X.a10, c*X.a11, c*X.a12, c*X.a13,
   c*X.a20, c*X.a21, c*X.a22, c*X.a23,
   c*X.a30, c*X.a31, c*X.a32, c*X.a33⟩

@[simp] lemma smul_a00 (c : R) (X : Mat4 R) :
    (smul c X).a00 = c * X.a00 := rfl

@[simp] lemma smul_a01 (c : R) (X : Mat4 R) :
    (smul c X).a01 = c * X.a01 := rfl

@[simp] lemma smul_a02 (c : R) (X : Mat4 R) :
    (smul c X).a02 = c * X.a02 := rfl

@[simp] lemma smul_a03 (c : R) (X : Mat4 R) :
    (smul c X).a03 = c * X.a03 := rfl

@[simp] lemma smul_a10 (c : R) (X : Mat4 R) :
    (smul c X).a10 = c * X.a10 := rfl

@[simp] lemma smul_a11 (c : R) (X : Mat4 R) :
    (smul c X).a11 = c * X.a11 := rfl

@[simp] lemma smul_a12 (c : R) (X : Mat4 R) :
    (smul c X).a12 = c * X.a12 := rfl

@[simp] lemma smul_a13 (c : R) (X : Mat4 R) :
    (smul c X).a13 = c * X.a13 := rfl

@[simp] lemma smul_a20 (c : R) (X : Mat4 R) :
    (smul c X).a20 = c * X.a20 := rfl

@[simp] lemma smul_a21 (c : R) (X : Mat4 R) :
    (smul c X).a21 = c * X.a21 := rfl

@[simp] lemma smul_a22 (c : R) (X : Mat4 R) :
    (smul c X).a22 = c * X.a22 := rfl

@[simp] lemma smul_a23 (c : R) (X : Mat4 R) :
    (smul c X).a23 = c * X.a23 := rfl

@[simp] lemma smul_a30 (c : R) (X : Mat4 R) :
    (smul c X).a30 = c * X.a30 := rfl

@[simp] lemma smul_a31 (c : R) (X : Mat4 R) :
    (smul c X).a31 = c * X.a31 := rfl

@[simp] lemma smul_a32 (c : R) (X : Mat4 R) :
    (smul c X).a32 = c * X.a32 := rfl

@[simp] lemma smul_a33 (c : R) (X : Mat4 R) :
    (smul c X).a33 = c * X.a33 := rfl

@[simp] lemma one_a00 :
    (1 : Mat4 R).a00 = 1 := rfl

@[simp] lemma one_a01 :
    (1 : Mat4 R).a01 = 0 := rfl

@[simp] lemma one_a02 :
    (1 : Mat4 R).a02 = 0 := rfl

@[simp] lemma one_a03 :
    (1 : Mat4 R).a03 = 0 := rfl

@[simp] lemma one_a10 :
    (1 : Mat4 R).a10 = 0 := rfl

@[simp] lemma one_a11 :
    (1 : Mat4 R).a11 = 1 := rfl

@[simp] lemma one_a12 :
    (1 : Mat4 R).a12 = 0 := rfl

@[simp] lemma one_a13 :
    (1 : Mat4 R).a13 = 0 := rfl

@[simp] lemma one_a20 :
    (1 : Mat4 R).a20 = 0 := rfl

@[simp] lemma one_a21 :
    (1 : Mat4 R).a21 = 0 := rfl

@[simp] lemma one_a22 :
    (1 : Mat4 R).a22 = 1 := rfl

@[simp] lemma one_a23 :
    (1 : Mat4 R).a23 = 0 := rfl

@[simp] lemma one_a30 :
    (1 : Mat4 R).a30 = 0 := rfl

@[simp] lemma one_a31 :
    (1 : Mat4 R).a31 = 0 := rfl

@[simp] lemma one_a32 :
    (1 : Mat4 R).a32 = 0 := rfl

@[simp] lemma one_a33 :
    (1 : Mat4 R).a33 = 1 := rfl

def det4 (A : Mat4 R) : R :=
  (A.a00 * A.a11 - A.a10 * A.a01) * (A.a22 * A.a33 - A.a32 * A.a23) +
  (A.a00 * A.a21 - A.a20 * A.a01) * (A.a32 * A.a13 - A.a12 * A.a33) +
  (A.a00 * A.a31 - A.a30 * A.a01) * (A.a12 * A.a23 - A.a22 * A.a13) +
  (A.a20 * A.a31 - A.a30 * A.a21) * (A.a02 * A.a13 - A.a12 * A.a03) +
  (A.a30 * A.a11 - A.a10 * A.a31) * (A.a02 * A.a23 - A.a22 * A.a03) +
  (A.a10 * A.a21 - A.a20 * A.a11) * (A.a02 * A.a33 - A.a32 * A.a03)

def E1 : Mat4 R := ⟨ 0,  0,  1,  0,   0,  0,  0, -1,   1,  0,  0,  0,   0, -1,  0,  0⟩
def E2 : Mat4 R := ⟨ 0,  0,  0,  1,   0,  0,  1,  0,   0,  1,  0,  0,   1,  0,  0,  0⟩
def E3 : Mat4 R := ⟨ 0,  0,  0,  1,   0,  0, -1,  0,   0,  1,  0,  0,  -1,  0,  0,  0⟩
def E4 : Mat4 R := ⟨ 0,  0,  1,  0,   0,  0,  0,  1,  -1,  0,  0,  0,   0, -1,  0,  0⟩

def omega : Mat4 R := ((E1 : Mat4 R) * E2) * E3 * E4

def E00 : Mat4 R := ⟨1,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩

def clVec (x1 x2 x3 x4 : R) : Mat4 R :=
  smul x1 E1 + smul x2 E2 + smul x3 E3 + smul x4 E4

def clBivec (p12 p13 p14 p23 p24 p34 : R) : Mat4 R :=
  smul p12 ((E1 : Mat4 R) * E2) +
  smul p13 ((E1 : Mat4 R) * E3) +
  smul p14 ((E1 : Mat4 R) * E4) +
  smul p23 ((E2 : Mat4 R) * E3) +
  smul p24 ((E2 : Mat4 R) * E4) +
  smul p34 ((E3 : Mat4 R) * E4)

end Mat4

set_option maxHeartbeats 0 in
theorem test_thm1 (M : Mat4 R) :
    let e1 := (Mat4.E1 : Mat4 R); let e2 := (Mat4.E2 : Mat4 R)
    let e3 := (Mat4.E3 : Mat4 R); let e4 := (Mat4.E4 : Mat4 R)
    let w  := (Mat4.omega : Mat4 R)
    let f4 := (1 + w) * (1 - e2 * e3)
    e1 * e1 = 1 ∧ e2 * e2 = 1 ∧ e3 * e3 = -(1 : Mat4 R) ∧ e4 * e4 = -(1 : Mat4 R) ∧
    e1 * e2 + e2 * e1 = 0 ∧ e1 * e3 + e3 * e1 = 0 ∧ e1 * e4 + e4 * e1 = 0 ∧
    e2 * e3 + e3 * e2 = 0 ∧ e2 * e4 + e4 * e2 = 0 ∧ e3 * e4 + e4 * e3 = 0 ∧
    w * w = 1 ∧
    f4 = Mat4.smul 4 Mat4.E00 ∧
    f4 * f4 = Mat4.smul 4 f4 ∧
    M * Mat4.E00 = ⟨M.a00, 0, 0, 0, M.a10, 0, 0, 0, M.a20, 0, 0, 0, M.a30, 0, 0, 0⟩ ∧
    Mat4.det4 (Mat4.E00 : Mat4 R) = 0 ∧
    Mat4.det4 ((1 : Mat4 R) - Mat4.E00) = 0 ∧
    Mat4.det4 ((Mat4.E00 : Mat4 R) + (1 - Mat4.E00)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · ext <;> simp [Mat4.E1, Mat4.E2, Mat4.E3, Mat4.E4, Mat4.omega, Mat4.E00] <;> ring
  · norm_num [Mat4.det4, Mat4.E00]
  · norm_num [Mat4.det4, Mat4.E00, Mat4.sub, Mat4.one]
  · norm_num [Mat4.det4, Mat4.E00, Mat4.add, Mat4.sub, Mat4.one]


theorem test_det4_mul (A B : Mat4 R) :
    Mat4.det4 (A * B) = Mat4.det4 A * Mat4.det4 B := by
  change Mat4.det4 (Mat4.mul A B) = Mat4.det4 A * Mat4.det4 B
  unfold Mat4.det4 Mat4.mul
  ring


example : ((Mat4.E1 : Mat4 R) * Mat4.E1).a00 = (1 : Mat4 R).a00 := by
  simp only [Mat4.mul_a00, Mat4.one_a00, Mat4.E1]
  ring

end ScratchClifford22
