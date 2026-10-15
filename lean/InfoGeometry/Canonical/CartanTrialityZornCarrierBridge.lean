import InfoGeometry.SuperGrassmannian.CartanTrialityZornProduct
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornMatrixVectorCarrierBridge

/-!
# Coordinate bridge for the repaired Section 49 Zorn carrier

The Section 49 file uses a record-valued `Vec3` and explicit `add`/`smul`
operations. `Canonical.ZornSpinor.ZornMatrix` uses `Fin 3 → R` vectors and
Mathlib's additive/module operations. This file identifies their coordinates
and proves compatibility with the already-defined products, units, and norms.
It introduces no second Zorn product or automorphism group.
-/

namespace InfoGeometry.SuperGrassmannian.CartanTrialityZorn

open InfoGeometry.Canonical

variable {R : Type*} [CommRing R]

/-- Convert the Section 49 three-coordinate record to a function vector. -/
def Vec3.toCanonical (u : Vec3 R) : Fin 3 → R := ![u.x, u.y, u.z]

/-- Convert a canonical function vector to the Section 49 record. -/
def Vec3.ofCanonical (u : Fin 3 → R) : Vec3 R := ⟨u 0, u 1, u 2⟩

omit [CommRing R] in
@[simp] theorem Vec3.ofCanonical_toCanonical (u : Vec3 R) :
    Vec3.ofCanonical (Vec3.toCanonical u) = u := by
  cases u
  rfl

omit [CommRing R] in
@[simp] theorem Vec3.toCanonical_ofCanonical (u : Fin 3 → R) :
    Vec3.toCanonical (Vec3.ofCanonical u) = u := by
  funext i
  fin_cases i <;> rfl

/-- Coordinate conversion from the repaired Section 49 carrier to the
canonical Zorn carrier. -/
def ZornMatrix.toCanonical (X : ZornMatrix R) :
    InfoGeometry.Canonical.ZornMatrix R :=
  ⟨X.a, X.b, X.u.toCanonical, X.v.toCanonical⟩

/-- Inverse coordinate conversion from the canonical Zorn carrier. -/
def ZornMatrix.ofCanonical (X : InfoGeometry.Canonical.ZornMatrix R) :
    ZornMatrix R :=
  ⟨X.a, Vec3.ofCanonical X.x, Vec3.ofCanonical X.y, X.b⟩

@[simp] theorem ZornMatrix.ofCanonical_toCanonical (X : ZornMatrix R) :
    ZornMatrix.ofCanonical (ZornMatrix.toCanonical X) = X := by
  cases X with
  | mk a u v b =>
      simp [ZornMatrix.toCanonical, ZornMatrix.ofCanonical]

@[simp] theorem ZornMatrix.toCanonical_ofCanonical
    (X : InfoGeometry.Canonical.ZornMatrix R) :
    ZornMatrix.toCanonical (ZornMatrix.ofCanonical X) = X := by
  cases X with
  | mk a b x y =>
      simp [ZornMatrix.toCanonical, ZornMatrix.ofCanonical]

/-- The coordinate conversion is a bijection of the two carriers. -/
def zornCarrierEquiv : ZornMatrix R ≃ InfoGeometry.Canonical.ZornMatrix R where
  toFun := ZornMatrix.toCanonical
  invFun := ZornMatrix.ofCanonical
  left_inv := ZornMatrix.ofCanonical_toCanonical
  right_inv := ZornMatrix.toCanonical_ofCanonical

@[simp] theorem Vec3.dot_toCanonical (u v : Vec3 R) :
    Vec3.dot u v = InfoGeometry.Canonical.ZornMatrix.dot
      u.toCanonical v.toCanonical := by
  cases u
  cases v
  simp [Vec3.dot, Vec3.toCanonical,
    InfoGeometry.Canonical.ZornMatrix.dot]

theorem Vec3.cross_toCanonical (u v : Vec3 R) :
    (Vec3.cross u v).toCanonical =
      InfoGeometry.Canonical.ZornMatrix.cross u.toCanonical v.toCanonical := by
  cases u
  cases v
  funext i
  fin_cases i <;>
    simp [Vec3.cross, Vec3.toCanonical,
      InfoGeometry.Canonical.ZornMatrix.cross]

/-- Conversion preserves the Section 49 explicit addition operation. -/
theorem ZornMatrix.toCanonical_add (X Y : ZornMatrix R) :
    ZornMatrix.toCanonical (ZornMatrix.add X Y) =
      ZornMatrix.toCanonical X + ZornMatrix.toCanonical Y := by
  cases X
  cases Y
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [ZornMatrix.add, ZornMatrix.toCanonical, Vec3.toCanonical]

/-- Conversion preserves the Section 49 explicit scalar operation. -/
theorem ZornMatrix.toCanonical_smul (r : R) (X : ZornMatrix R) :
    ZornMatrix.toCanonical (ZornMatrix.smul r X) =
      r • ZornMatrix.toCanonical X := by
  cases X
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [ZornMatrix.smul, ZornMatrix.toCanonical, Vec3.toCanonical]

/-- Conversion intertwines the two existing Zorn products. -/
theorem ZornMatrix.toCanonical_mul (X Y : ZornMatrix R) :
    ZornMatrix.toCanonical (ZornMatrix.mul X Y) =
      InfoGeometry.Canonical.ZornMatrix.mul
        (ZornMatrix.toCanonical X) (ZornMatrix.toCanonical Y) := by
  cases X with
  | mk xa xu xv xb =>
    cases Y with
    | mk ya yu yv yb =>
      apply InfoGeometry.Canonical.ZornMatrix.ext
      · simp [ZornMatrix.toCanonical, ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.mul, Vec3.dot_toCanonical]
      · simp [ZornMatrix.toCanonical, ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.mul, Vec3.dot_toCanonical]
      · ext i
        fin_cases i <;>
          simp [ZornMatrix.toCanonical, ZornMatrix.mul, Vec3.toCanonical,
            Vec3.cross, InfoGeometry.Canonical.ZornMatrix.mul,
            InfoGeometry.Canonical.ZornMatrix.cross]
      · ext i
        fin_cases i <;>
          simp [ZornMatrix.toCanonical, ZornMatrix.mul, Vec3.toCanonical,
            Vec3.cross, InfoGeometry.Canonical.ZornMatrix.mul,
            InfoGeometry.Canonical.ZornMatrix.cross] <;> ring

/-- The explicit Section 49 unit is sent to the canonical unit. -/
theorem ZornMatrix.toCanonical_one :
    ZornMatrix.toCanonical (ZornMatrix.one : ZornMatrix R) =
      (1 : InfoGeometry.Canonical.ZornMatrix R) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;>
      simp [ZornMatrix.toCanonical, ZornMatrix.one, Vec3.toCanonical]
  · funext i
    fin_cases i <;>
      simp [ZornMatrix.toCanonical, ZornMatrix.one, Vec3.toCanonical]

/-- The Section 49 determinant agrees with the canonical quadratic norm. -/
theorem ZornMatrix.toCanonical_det (X : ZornMatrix R) :
    ZornMatrix.det X =
      InfoGeometry.Algebra.ZornVectorMatrix.norm
        (InfoGeometry.Canonical.zornMatrixToVector (ZornMatrix.toCanonical X)) := by
  cases X
  simp [ZornMatrix.det, ZornMatrix.toCanonical,
    InfoGeometry.Canonical.zornMatrixToVector,
    InfoGeometry.Algebra.ZornVectorMatrix.norm,
    InfoGeometry.Algebra.ZornVec3.dot,
    InfoGeometry.Canonical.ZornMatrix.dot, Vec3.toCanonical,
    Fin.sum_univ_three]

end InfoGeometry.SuperGrassmannian.CartanTrialityZorn
