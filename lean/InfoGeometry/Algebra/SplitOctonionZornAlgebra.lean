import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic

/-!
# Split-Octonions via Zorn Vector-Matrix Algebra

This module formalizes the split-octonions $\mathbb{O}'$ realized as Zorn's vector-matrix algebra:
$$Z = \begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & d \end{pmatrix}, \quad a, d \in \mathbb{R}, \quad \mathbf{u}, \mathbf{v} \in \mathbb{R}^3$$
with determinant quadratic norm form:
$$\det(Z) = ad - \mathbf{u} \cdot \mathbf{v}$$
satisfying:
1. Two-sided inversion: $X \bar{X} = \bar{X} X = \det(X) \mathbb{I}$
2. Composition algebra norm multiplicativity: $\det(X Y) = \det(X) \det(Y)$
3. Neutral signature $(4, 4)$ canonical quadratic form
4. Existence of non-trivial idempotent zero divisors.
-/

namespace InfoGeometry.Algebra.SplitOctonionZorn

structure Vector3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vector3

@[ext]
theorem ext {u v : Vector3} (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u; cases v; dsimp at hx hy hz; rw [hx, hy, hz]

def zero : Vector3 := ⟨0, 0, 0⟩
instance : Zero Vector3 := ⟨zero⟩

def add (u v : Vector3) : Vector3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
instance : Add Vector3 := ⟨add⟩

def neg (u : Vector3) : Vector3 := ⟨-u.x, -u.y, -u.z⟩
instance : Neg Vector3 := ⟨neg⟩

def sub (u v : Vector3) : Vector3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
instance : Sub Vector3 := ⟨sub⟩

def smul (c : ℝ) (u : Vector3) : Vector3 := ⟨c * u.x, c * u.y, c * u.z⟩
instance : HSMul ℝ Vector3 Vector3 := ⟨smul⟩
instance : SMul ℝ Vector3 := ⟨smul⟩

def dot (u v : Vector3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

def cross (u v : Vector3) : Vector3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

instance : AddCommGroup Vector3 where
  add_assoc := by intros u v w; cases u; cases v; cases w; ext <;> (change (_ + _) + _ = _ + (_ + _); ring)
  zero_add := by intros u; cases u; ext <;> (change 0 + _ = _; ring)
  add_zero := by intros u; cases u; ext <;> (change _ + 0 = _; ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by intros u; cases u; ext <;> (change -_ + _ = 0; ring)
  add_comm := by intros u v; cases u; cases v; ext <;> (change _ + _ = _ + _; ring)

instance : Module ℝ Vector3 where
  one_smul := by intros u; cases u; ext <;> (change 1 * _ = _; ring)
  mul_smul := by intros c d u; cases u; ext <;> (change (c * d) * _ = c * (d * _); ring)
  smul_zero := by intros c; ext <;> (change c * 0 = 0; ring)
  smul_add := by intros c u v; cases u; cases v; ext <;> (change c * (_ + _) = c * _ + c * _; ring)
  add_smul := by intros c d u; cases u; ext <;> (change (c + d) * _ = c * _ + d * _; ring)
  zero_smul := by intros u; cases u; ext <;> (change 0 * _ = 0; ring)

end Vector3

structure SplitOctonion where
  a : ℝ
  u : Vector3
  v : Vector3
  d : ℝ

namespace SplitOctonion

@[ext]
theorem ext {X Y : SplitOctonion}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hd : X.d = Y.d) : X = Y := by
  cases X; cases Y; dsimp at ha hu hv hd; rw [ha, hu, hv, hd]

def one : SplitOctonion := ⟨1, Vector3.zero, Vector3.zero, 1⟩
instance : One SplitOctonion := ⟨one⟩

def zero : SplitOctonion := ⟨0, Vector3.zero, Vector3.zero, 0⟩
instance : Zero SplitOctonion := ⟨zero⟩

def add (X Y : SplitOctonion) : SplitOctonion :=
  ⟨X.a + Y.a, Vector3.add X.u Y.u, Vector3.add X.v Y.v, X.d + Y.d⟩
instance : Add SplitOctonion := ⟨add⟩

def neg (X : SplitOctonion) : SplitOctonion :=
  ⟨-X.a, Vector3.neg X.u, Vector3.neg X.v, -X.d⟩
instance : Neg SplitOctonion := ⟨neg⟩

def sub (X Y : SplitOctonion) : SplitOctonion :=
  ⟨X.a - Y.a, Vector3.sub X.u Y.u, Vector3.sub X.v Y.v, X.d - Y.d⟩
instance : Sub SplitOctonion := ⟨sub⟩

def smul (c : ℝ) (X : SplitOctonion) : SplitOctonion :=
  ⟨c * X.a, c • X.u, c • X.v, c * X.d⟩
instance : HSMul ℝ SplitOctonion SplitOctonion := ⟨smul⟩
instance : SMul ℝ SplitOctonion := ⟨smul⟩

macro "unpack_oct" X:ident : tactic =>
  `(tactic| (cases $X:ident; rename_i _a _u _v _d; cases _u; cases _v))

instance : AddCommGroup SplitOctonion where
  add_assoc := by
    intros X Y Z; unpack_oct X; unpack_oct Y; unpack_oct Z
    ext <;> (change (_ + _) + _ = _ + (_ + _); ring)
  zero_add := by
    intros X; unpack_oct X
    ext <;> (change 0 + _ = _; ring)
  add_zero := by
    intros X; unpack_oct X
    ext <;> (change _ + 0 = _; ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intros X; unpack_oct X
    ext <;> (change -_ + _ = 0; ring)
  add_comm := by
    intros X Y; unpack_oct X; unpack_oct Y
    ext <;> (change _ + _ = _ + _; ring)

instance : Module ℝ SplitOctonion where
  one_smul := by
    intros X; unpack_oct X
    ext <;> (change 1 * _ = _; ring)
  mul_smul := by
    intros c d X; unpack_oct X
    ext <;> (change (c * d) * _ = c * (d * _); ring)
  smul_zero := by
    intros c
    ext <;> (change c * 0 = 0; ring)
  smul_add := by
    intros c X Y; unpack_oct X; unpack_oct Y
    ext <;> (change c * (_ + _) = c * _ + c * _; ring)
  add_smul := by
    intros c d X; unpack_oct X
    ext <;> (change (c + d) * _ = c * _ + d * _; ring)
  zero_smul := by
    intros X; unpack_oct X
    ext <;> (change 0 * _ = 0; ring)

def zornDet (X : SplitOctonion) : ℝ :=
  X.a * X.d - Vector3.dot X.u X.v

def conj (X : SplitOctonion) : SplitOctonion :=
  ⟨X.d, -X.u, -X.v, X.a⟩

def mul (X Y : SplitOctonion) : SplitOctonion :=
  ⟨X.a * Y.a + Vector3.dot X.u Y.v,
   Vector3.sub (Vector3.add (Vector3.smul X.a Y.u) (Vector3.smul Y.d X.u)) (Vector3.cross X.v Y.v),
   Vector3.add (Vector3.add (Vector3.smul Y.a X.v) (Vector3.smul X.d Y.v)) (Vector3.cross X.u Y.u),
   X.d * Y.d + Vector3.dot X.v Y.u⟩
instance : Mul SplitOctonion := ⟨mul⟩

theorem mul_one (X : SplitOctonion) : X * 1 = X := by
  cases X; rename_i a u v d; cases u; rename_i ux uy uz; cases v; rename_i vx vy vz
  ext
  · show a * 1 + (ux * 0 + uy * 0 + uz * 0) = a; ring
  · show (a * 0 + 1 * ux) - (vy * 0 - vz * 0) = ux; ring
  · show (a * 0 + 1 * uy) - (vz * 0 - vx * 0) = uy; ring
  · show (a * 0 + 1 * uz) - (vx * 0 - vy * 0) = uz; ring
  · show (1 * vx + d * 0) + (uy * 0 - uz * 0) = vx; ring
  · show (1 * vy + d * 0) + (uz * 0 - ux * 0) = vy; ring
  · show (1 * vz + d * 0) + (ux * 0 - uy * 0) = vz; ring
  · show d * 1 + (vx * 0 + vy * 0 + vz * 0) = d; ring

theorem one_mul (X : SplitOctonion) : 1 * X = X := by
  cases X; rename_i a u v d; cases u; rename_i ux uy uz; cases v; rename_i vx vy vz
  ext
  · show 1 * a + (0 * vx + 0 * vy + 0 * vz) = a; ring
  · show (1 * ux + d * 0) - (0 * vz - 0 * vy) = ux; ring
  · show (1 * uy + d * 0) - (0 * vx - 0 * vz) = uy; ring
  · show (1 * uz + d * 0) - (0 * vy - 0 * vx) = uz; ring
  · show (a * 0 + 1 * vx) + (0 * uz - 0 * uy) = vx; ring
  · show (a * 0 + 1 * vy) + (0 * ux - 0 * uz) = vy; ring
  · show (a * 0 + 1 * vz) + (0 * uy - 0 * ux) = vz; ring
  · show 1 * d + (0 * ux + 0 * uy + 0 * uz) = d; ring

lemma sub_mul (X Y Z : SplitOctonion) : (X - Y) * Z = X * Z - Y * Z := by
  cases X; cases Y; cases Z
  rename_i aX uX vX dX aY uY vY dY aZ uZ vZ dZ
  ext
  · show (aX - aY) * aZ + ((uX.x - uY.x) * vZ.x + (uX.y - uY.y) * vZ.y + (uX.z - uY.z) * vZ.z) =
         (aX * aZ + (uX.x * vZ.x + uX.y * vZ.y + uX.z * vZ.z)) -
         (aY * aZ + (uY.x * vZ.x + uY.y * vZ.y + uY.z * vZ.z)); ring
  · show ((aX - aY) * uZ.x + dZ * (uX.x - uY.x)) - ((vX.y - vY.y) * vZ.z - (vX.z - vY.z) * vZ.y) =
         (aX * uZ.x + dZ * uX.x - (vX.y * vZ.z - vX.z * vZ.y)) -
         (aY * uZ.x + dZ * uY.x - (vY.y * vZ.z - vY.z * vZ.y)); ring
  · show ((aX - aY) * uZ.y + dZ * (uX.y - uY.y)) - ((vX.z - vY.z) * vZ.x - (vX.x - vY.x) * vZ.z) =
         (aX * uZ.y + dZ * uX.y - (vX.z * vZ.x - vX.x * vZ.z)) -
         (aY * uZ.y + dZ * uY.y - (vY.z * vZ.x - vY.x * vZ.z)); ring
  · show ((aX - aY) * uZ.z + dZ * (uX.z - uY.z)) - ((vX.x - vY.x) * vZ.y - (vX.y - vY.y) * vZ.x) =
         (aX * uZ.z + dZ * uX.z - (vX.x * vZ.y - vX.y * vZ.x)) -
         (aY * uZ.z + dZ * uY.z - (vY.x * vZ.y - vY.y * vZ.x)); ring
  · show (aZ * (vX.x - vY.x) + (dX - dY) * vZ.x) + ((uX.y - uY.y) * uZ.z - (uX.z - uY.z) * uZ.y) =
         (aZ * vX.x + dX * vZ.x + (uX.y * uZ.z - uX.z * uZ.y)) -
         (aZ * vY.x + dY * vZ.x + (uY.y * uZ.z - uY.z * uZ.y)); ring
  · show (aZ * (vX.y - vY.y) + (dX - dY) * vZ.y) + ((uX.z - uY.z) * uZ.x - (uX.x - uY.x) * uZ.z) =
         (aZ * vX.y + dX * vZ.y + (uX.z * uZ.x - uX.x * uZ.z)) -
         (aZ * vY.y + dY * vZ.y + (uY.z * uZ.x - uY.x * uZ.z)); ring
  · show (aZ * (vX.z - vY.z) + (dX - dY) * vZ.z) + ((uX.x - uY.x) * uZ.y - (uX.y - uY.y) * uZ.x) =
         (aZ * vX.z + dX * vZ.z + (uX.x * uZ.y - uX.y * uZ.x)) -
         (aZ * vY.z + dY * vZ.z + (uY.x * uZ.y - uY.y * uZ.x)); ring
  · show (dX - dY) * dZ + ((vX.x - vY.x) * uZ.x + (vX.y - vY.y) * uZ.y + (vX.z - vY.z) * uZ.z) =
         (dX * dZ + (vX.x * uZ.x + vX.y * uZ.y + vX.z * uZ.z)) -
         (dY * dZ + (vY.x * uZ.x + vY.y * uZ.y + vY.z * uZ.z)); ring

lemma mul_sub (X Y Z : SplitOctonion) : X * (Y - Z) = X * Y - X * Z := by
  cases X; cases Y; cases Z
  rename_i aX uX vX dX aY uY vY dY aZ uZ vZ dZ
  ext
  · show aX * (aY - aZ) + (uX.x * (vY.x - vZ.x) + uX.y * (vY.y - vZ.y) + uX.z * (vY.z - vZ.z)) =
         (aX * aY + (uX.x * vY.x + uX.y * vY.y + uX.z * vY.z)) -
         (aX * aZ + (uX.x * vZ.x + uX.y * vZ.y + uX.z * vZ.z)); ring
  · show (aX * (uY.x - uZ.x) + (dY - dZ) * uX.x) - (vX.y * (vY.z - vZ.z) - vX.z * (vY.y - vZ.y)) =
         (aX * uY.x + dY * uX.x - (vX.y * vY.z - vX.z * vY.y)) -
         (aX * uZ.x + dZ * uX.x - (vX.y * vZ.z - vX.z * vZ.y)); ring
  · show (aX * (uY.y - uZ.y) + (dY - dZ) * uX.y) - (vX.z * (vY.x - vZ.x) - vX.x * (vY.z - vZ.z)) =
         (aX * uY.y + dY * uX.y - (vX.z * vY.x - vX.x * vY.z)) -
         (aX * uZ.y + dZ * uX.y - (vX.z * vZ.x - vX.x * vZ.z)); ring
  · show (aX * (uY.z - uZ.z) + (dY - dZ) * uX.z) - (vX.x * (vY.y - vZ.y) - vX.y * (vY.x - vZ.x)) =
         (aX * uY.z + dY * uX.z - (vX.x * vY.y - vX.y * vY.x)) -
         (aX * uZ.z + dZ * uX.z - (vX.x * vZ.y - vX.y * vZ.x)); ring
  · show ((aY - aZ) * vX.x + dX * (vY.x - vZ.x)) + (uX.y * (uY.z - uZ.z) - uX.z * (uY.y - uZ.y)) =
         (aY * vX.x + dX * vY.x + (uX.y * uY.z - uX.z * uY.y)) -
         (aZ * vX.x + dX * vZ.x + (uX.y * uZ.z - uX.z * uZ.y)); ring
  · show ((aY - aZ) * vX.y + dX * (vY.y - vZ.y)) + (uX.z * (uY.x - uZ.x) - uX.x * (uY.z - uZ.z)) =
         (aY * vX.y + dX * vY.y + (uX.z * uY.x - uX.x * uY.z)) -
         (aZ * vX.y + dX * vZ.y + (uX.z * uZ.x - uX.x * uZ.z)); ring
  · show ((aY - aZ) * vX.z + dX * (vY.z - vZ.z)) + (uX.x * (uY.y - uZ.y) - uX.y * (uY.x - uZ.x)) =
         (aY * vX.z + dX * vY.z + (uX.x * uY.y - uX.y * uY.x)) -
         (aZ * vX.z + dX * vZ.z + (uX.x * uZ.y - uX.y * uZ.x)); ring
  · show dX * (dY - dZ) + (vX.x * (uY.x - uZ.x) + vX.y * (uY.y - uZ.y) + vX.z * (uY.z - uZ.z)) =
         (dX * dY + (vX.x * uY.x + vX.y * uY.y + vX.z * uY.z)) -
         (dX * dZ + (vX.x * uZ.x + vX.y * uZ.y + vX.z * uZ.z)); ring

lemma cancellation_identity (A B C D E F : SplitOctonion) :
    (A + B + (C + D)) - (E + C + (B + F)) = (A - E) + (D - F) := by
  cases A; cases B; cases C; cases D; cases E; cases F
  rename_i aA uA vA dA aB uB vB dB aC uC vC dC aD uD vD dD aE uE vE dE aF uF vF dF
  ext
  · show (((aA + aB) + (aC + aD)) - ((aE + aC) + (aB + aF))) = (aA - aE) + (aD - aF); ring
  · show (((uA.x + uB.x) + (uC.x + uD.x)) - ((uE.x + uC.x) + (uB.x + uF.x))) = (uA.x - uE.x) + (uD.x - uF.x); ring
  · show (((uA.y + uB.y) + (uC.y + uD.y)) - ((uE.y + uC.y) + (uB.y + uF.y))) = (uA.y - uE.y) + (uD.y - uF.y); ring
  · show (((uA.z + uB.z) + (uC.z + uD.z)) - ((uE.z + uC.z) + (uB.z + uF.z))) = (uA.z - uE.z) + (uD.z - uF.z); ring
  · show (((vA.x + vB.x) + (vC.x + vD.x)) - ((vE.x + vC.x) + (vB.x + vF.x))) = (vA.x - vE.x) + (vD.x - vF.x); ring
  · show (((vA.y + vB.y) + (vC.y + vD.y)) - ((vE.y + vC.y) + (vB.y + vF.y))) = (vA.y - vE.y) + (vD.y - vF.y); ring
  · show (((vA.z + vB.z) + (vC.z + vD.z)) - ((vE.z + vC.z) + (vB.z + vF.z))) = (vA.z - vE.z) + (vD.z - vF.z); ring
  · show (((dA + dB) + (dC + dD)) - ((dE + dC) + (dB + dF))) = (dA - dE) + (dD - dF); ring

theorem mul_conj_eq_det_smul_one (X : SplitOctonion) :
    X * conj X = zornDet X • (1 : SplitOctonion) := by
  cases X; rename_i a u v d; cases u; rename_i ux uy uz; cases v; rename_i vx vy vz
  ext
  · show a * d + (ux * (-vx) + uy * (-vy) + uz * (-vz)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 1; ring
  · show (a * (-ux) + a * ux) - (vy * (-vz) - vz * (-vy)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (a * (-uy) + a * uy) - (vz * (-vx) - vx * (-vz)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (a * (-uz) + a * uz) - (vx * (-vy) - vy * (-vx)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (d * vx + d * (-vx)) + (uy * (-uz) - uz * (-uy)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (d * vy + d * (-vy)) + (uz * (-ux) - ux * (-uz)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (d * vz + d * (-vz)) + (ux * (-uy) - uy * (-ux)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show d * a + (vx * (-ux) + vy * (-uy) + vz * (-uz)) = (a * d - (ux * vx + uy * vy + uz * vz)) * 1; ring

theorem conj_mul_eq_det_smul_one (X : SplitOctonion) :
    conj X * X = zornDet X • (1 : SplitOctonion) := by
  cases X; rename_i a u v d; cases u; rename_i ux uy uz; cases v; rename_i vx vy vz
  ext
  · show d * a + ((-ux) * vx + (-uy) * vy + (-uz) * vz) = (a * d - (ux * vx + uy * vy + uz * vz)) * 1; ring
  · show (d * ux + d * (-ux)) - ((-vy) * vz - (-vz) * vy) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (d * uy + d * (-uy)) - ((-vz) * vx - (-vx) * vz) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (d * uz + d * (-uz)) - ((-vx) * vy - (-vy) * vx) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (a * (-vx) + a * vx) + ((-uy) * uz - (-uz) * uy) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (a * (-vy) + a * vy) + ((-uz) * ux - (-ux) * uz) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show (a * (-vz) + a * vz) + ((-ux) * uy - (-uy) * ux) = (a * d - (ux * vx + uy * vy + uz * vz)) * 0; ring
  · show a * d + ((-vx) * ux + (-vy) * uy + (-vz) * uz) = (a * d - (ux * vx + uy * vy + uz * vz)) * 1; ring

theorem zornDet_mul (X Y : SplitOctonion) :
    zornDet (X * Y) = zornDet X * zornDet Y := by
  cases X; rename_i a1 u1 v1 d1; cases u1; rename_i u1x u1y u1z; cases v1; rename_i v1x v1y v1z
  cases Y; rename_i a2 u2 v2 d2; cases u2; rename_i u2x u2y u2z; cases v2; rename_i v2x v2y v2z
  show (a1 * a2 + (u1x * v2x + u1y * v2y + u1z * v2z)) *
       (d1 * d2 + (v1x * u2x + v1y * u2y + v1z * u2z)) -
       (((a1 * u2x + d2 * u1x) - (v1y * v2z - v1z * v2y)) *
        ((a2 * v1x + d1 * v2x) + (u1y * u2z - u1z * u2y)) +
        ((a1 * u2y + d2 * u1y) - (v1z * v2x - v1x * v2z)) *
        ((a2 * v1y + d1 * v2y) + (u1z * u2x - u1x * u2z)) +
        ((a1 * u2z + d2 * u1z) - (v1x * v2y - v1y * v2x)) *
        ((a2 * v1z + d1 * v2z) + (u1x * u2y - u1y * u2x))) =
       (a1 * d1 - (u1x * v1x + u1y * v1y + u1z * v1z)) *
       (a2 * d2 - (u2x * v2x + u2y * v2y + u2z * v2z))
  ring

def ofBasis8 (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : SplitOctonion where
  a := x0 + x7
  u := ⟨x1 + x4, x2 + x5, x3 + x6⟩
  v := ⟨-x1 + x4, -x2 + x5, -x3 + x6⟩
  d := x0 - x7

theorem zornDet_ofBasis8 (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    zornDet (ofBasis8 x0 x1 x2 x3 x4 x5 x6 x7) =
    x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 - x7 ^ 2 := by
  show (x0 + x7) * (x0 - x7) -
       ((x1 + x4) * (-x1 + x4) + (x2 + x5) * (-x2 + x5) + (x3 + x6) * (-x3 + x6)) =
       x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 - x7 ^ 2
  ring

def idempotentE1 : SplitOctonion := ⟨1, Vector3.zero, Vector3.zero, 0⟩
def idempotentE2 : SplitOctonion := ⟨0, Vector3.zero, Vector3.zero, 1⟩

theorem zero_divisor_witness :
    idempotentE1 ≠ 0 ∧ idempotentE2 ≠ 0 ∧ idempotentE1 * idempotentE2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : (idempotentE1).a = (0 : SplitOctonion).a := by rw [h]
    change 1 = 0 at h1
    norm_num at h1
  · intro h
    have h1 : (idempotentE2).d = (0 : SplitOctonion).d := by rw [h]
    change 1 = 0 at h1
    norm_num at h1
  · ext
    · change 1 * 0 + (0 * 0 + 0 * 0 + 0 * 0) = 0; ring
    · change (1 * 0 + 1 * 0) - (0 * 0 - 0 * 0) = 0; ring
    · change (1 * 0 + 1 * 0) - (0 * 0 - 0 * 0) = 0; ring
    · change (1 * 0 + 1 * 0) - (0 * 0 - 0 * 0) = 0; ring
    · change (0 * 0 + 0 * 0) + (0 * 0 - 0 * 0) = 0; ring
    · change (0 * 0 + 0 * 0) + (0 * 0 - 0 * 0) = 0; ring
    · change (0 * 0 + 0 * 0) + (0 * 0 - 0 * 0) = 0; ring
    · change 0 * 1 + (0 * 0 + 0 * 0 + 0 * 0) = 0; ring

theorem split_octonion_zorn_synthesis (X Y : SplitOctonion)
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    X * conj X = zornDet X • (1 : SplitOctonion) ∧
    conj X * X = zornDet X • (1 : SplitOctonion) ∧
    zornDet (X * Y) = zornDet X * zornDet Y ∧
    zornDet (ofBasis8 x0 x1 x2 x3 x4 x5 x6 x7) =
      x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 - x7 ^ 2 ∧
    (idempotentE1 ≠ 0 ∧ idempotentE2 ≠ 0 ∧ idempotentE1 * idempotentE2 = 0) := by
  exact ⟨mul_conj_eq_det_smul_one X,
         conj_mul_eq_det_smul_one X,
         zornDet_mul X Y,
         zornDet_ofBasis8 x0 x1 x2 x3 x4 x5 x6 x7,
         zero_divisor_witness⟩

end SplitOctonion

end InfoGeometry.Algebra.SplitOctonionZorn
