import InfoGeometry.Algebra.KingdonAlgebra
import InfoGeometry.Physics.ZornMatrixSU3.ZornMatrixCore
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-!
# The real split octonion as a three-dimensional Kingdon target
-/

namespace KingdonSplitOctonion

open InfoGeometry.Algebra.Kingdon
open InfoGeometry.Physics.ZornMatrixSU3

instance : NonAssocRing ZornMatrix where
  zero_mul := zero_mul_zorn
  mul_zero := mul_zero_zorn
  left_distrib := mul_add_zorn
  right_distrib := add_mul_zorn
  one_mul := one_mul_zorn
  mul_one := mul_one_zorn

instance : IsScalarTower ℝ ZornMatrix ZornMatrix where
  smul_assoc := smul_mul_zorn

instance : SMulCommClass ℝ ZornMatrix ZornMatrix where
  smul_comm r X Y := (mul_smul_zorn r X Y).symm

@[simp] theorem mul_eq_owner (X Y : ZornMatrix) :
    X * Y = InfoGeometry.Physics.ZornMatrixSU3.mul X Y := rfl

@[simp] theorem add_eq_owner (X Y : ZornMatrix) :
    X + Y = InfoGeometry.Physics.ZornMatrixSU3.add X Y := rfl

@[simp] theorem smul_eq_owner (r : ℝ) (X : ZornMatrix) :
    r • X = InfoGeometry.Physics.ZornMatrixSU3.smul r X := rfl

@[simp] theorem neg_eq_owner (X : ZornMatrix) :
    -X = InfoGeometry.Physics.ZornMatrixSU3.neg X := rfl

@[simp] theorem sub_eq_owner (X Y : ZornMatrix) :
    X - Y = InfoGeometry.Physics.ZornMatrixSU3.add X
      (InfoGeometry.Physics.ZornMatrixSU3.neg Y) := rfl

macro "zorn_ring" : tactic =>
  `(tactic|
    (simp [mul, Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring))

/-- The concrete real Zorn split-octonion multiplication is left alternative. -/
theorem zorn_left_alternative (X Y : ZornMatrix) : (X * X) * Y = X * (X * Y) := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  ext
  · zorn_ring
  · zorn_ring
  · rename_i i; fin_cases i <;> zorn_ring
  · rename_i i; fin_cases i <;> zorn_ring

/-- The concrete real Zorn split-octonion multiplication is right alternative. -/
theorem zorn_right_alternative (X Y : ZornMatrix) : (Y * X) * X = Y * (X * X) := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  ext
  · zorn_ring
  · zorn_ring
  · rename_i i; fin_cases i <;> zorn_ring
  · rename_i i; fin_cases i <;> zorn_ring

abbrev ThreeSpace := Fin 3 → ℝ

/-- Twice the Euclidean dot form, matching the Kingdon anticommutator normalization. -/
def formedBilin : LinearMap.BilinForm ℝ ThreeSpace :=
  LinearMap.mk₂ ℝ (fun u v => 2 * Physics.ZornMatrixSU3.dotProduct u v)
    (fun u v w => by simp [Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]; ring)
    (fun r u v => by simp [Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]; ring)
    (fun u v w => by simp [Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]; ring)
    (fun r u v => by simp [Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]; ring)

/-- Symmetric three-space insertion into the off-diagonal Zorn coordinates. -/
def generator : ThreeSpace →ₗ[ℝ] ZornMatrix where
  toFun v := ⟨0, 0, v, v⟩
  map_add' u v := by ext i <;> simp [add]
  map_smul' r v := by ext i <;> simp [smul]

/-- The concrete generators satisfy the Kingdon quadratic relation. -/
theorem generator_quadratic (u v : ThreeSpace) :
    generator u * generator v + generator v * generator u =
      formedBilin u v • (1 : ZornMatrix) := by
  ext
  · simp [generator, formedBilin, mul, add, smul, Physics.ZornMatrixSU3.dotProduct,
      crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · simp [generator, formedBilin, mul, add, smul, Physics.ZornMatrixSU3.dotProduct,
      crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [generator, formedBilin, mul, add, smul,
      Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [generator, formedBilin, mul, add, smul,
      Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

/-- The concrete generators collectively anti-associate. -/
theorem generator_antiassociate (u v w : ThreeSpace) :
    (generator u * generator v) * generator w =
      generator w * (generator v * generator u) := by
  ext
  · simp [generator, mul, Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · simp [generator, mul, Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [generator, mul,
      Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [generator, mul,
      Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

/-- The universal Kingdon homomorphism into the real Zorn split octonions. -/
noncomputable def realization :
    Kingdon.Algebra ℝ ThreeSpace formedBilin →+* ZornMatrix :=
  Kingdon.Algebra.liftOfLinear formedBilin generator
    zorn_left_alternative zorn_right_alternative
    generator_quadratic generator_antiassociate

@[simp] theorem realization_ι (v : ThreeSpace) :
    realization (Kingdon.Algebra.ι formedBilin v) = generator v := by
  exact Kingdon.Algebra.liftOfLinear_ι formedBilin generator
    zorn_left_alternative zorn_right_alternative
    generator_quadratic generator_antiassociate v

abbrev AbstractKingdon := Kingdon.Algebra ℝ ThreeSpace formedBilin

def basisVec (i : Fin 3) : ThreeSpace := fun j => if j = i then 1 else 0

theorem threeSpace_eq_basis_sum (v : ThreeSpace) :
    v = v 0 • basisVec 0 + v 1 • basisVec 1 + v 2 • basisVec 2 := by
  ext i
  fin_cases i <;> simp [basisVec]

noncomputable def scalar (r : ℝ) : AbstractKingdon :=
  Kingdon.Algebra.mk formedBilin (Unitization.inl r)

noncomputable def basisGenerator (i : Fin 3) : AbstractKingdon :=
  Kingdon.Algebra.ι formedBilin (basisVec i)

theorem scalar_eq_smul_one (r : ℝ) : scalar r = r • (1 : AbstractKingdon) := by
  simpa [scalar] using
    (Kingdon.Algebra.scalar_mul formedBilin r (1 : AbstractKingdon))

@[simp] theorem scalar_zero : scalar 0 = 0 := by
  simp [scalar]

theorem formedBilin_basisVec (i j : Fin 3) :
    formedBilin (basisVec i) (basisVec j) = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [formedBilin, basisVec, Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

theorem basisGenerator_sq (i : Fin 3) :
    basisGenerator i * basisGenerator i = 1 := by
  have h := Kingdon.Algebra.quadratic formedBilin (basisVec i) (basisVec i)
  rw [formedBilin_basisVec, if_pos rfl] at h
  change basisGenerator i * basisGenerator i + basisGenerator i * basisGenerator i = scalar 2 at h
  rw [scalar_eq_smul_one] at h
  have hs := congrArg (fun x : AbstractKingdon => ((2 : ℝ)⁻¹) • x) h
  norm_num [smul_add, ← add_smul] at hs
  calc
    basisGenerator i * basisGenerator i = (1 / 2 : ℝ) • (2 : ℝ) • (1 : AbstractKingdon) := hs
    _ = 1 := by rw [← mul_smul]; norm_num

theorem basisGenerator_anticomm {i j : Fin 3} (hij : i ≠ j) :
    basisGenerator i * basisGenerator j = -(basisGenerator j * basisGenerator i) := by
  have h := Kingdon.Algebra.quadratic formedBilin (basisVec i) (basisVec j)
  rw [formedBilin_basisVec, if_neg hij] at h
  change basisGenerator i * basisGenerator j + basisGenerator j * basisGenerator i = scalar 0 at h
  rw [scalar_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem mul_neg_abstract (a b : AbstractKingdon) : a * (-b) = -(a * b) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← mul_add, neg_add_cancel, mul_zero]

theorem neg_mul_abstract (a b : AbstractKingdon) : (-a) * b = -(a * b) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_mul, neg_add_cancel, zero_mul]

theorem basisBivector_sq {i j : Fin 3} (hij : i ≠ j) :
    (basisGenerator i * basisGenerator j) * (basisGenerator i * basisGenerator j) = -1 := by
  let x := basisGenerator i
  let y := basisGenerator j
  let q := x * y
  have hxy : x * y = -(y * x) := basisGenerator_anticomm hij
  have hyx : y * x = -q := by
    have hn := congrArg (fun z : AbstractKingdon => -z) hxy
    simpa [q] using hn.symm
  have hxx : x * x = 1 := basisGenerator_sq i
  have hyy : y * y = 1 := basisGenerator_sq j
  have hqx : q * x = -y := by
    calc
      q * x = x * (y * x) := Kingdon.Algebra.flexible formedBilin x y
      _ = x * (-q) := by rw [hyx]
      _ = -(x * q) := mul_neg_abstract x q
      _ = -((x * x) * y) := by
        rw [Kingdon.Algebra.alternative_left formedBilin x y]
      _ = -y := by rw [hxx, one_mul]
  have hqy : q * y = x := by
    calc
      q * y = x * (y * y) := Kingdon.Algebra.alternative_right formedBilin y x
      _ = x := by rw [hyy, mul_one]
  have hyq : y * q = -x := by
    calc
      y * q = (y * x) * y := (Kingdon.Algebra.flexible formedBilin y x).symm
      _ = (-q) * y := by rw [hyx]
      _ = -(q * y) := neg_mul_abstract q y
      _ = -x := by rw [hqy]
  have h := Kingdon.Algebra.associator_swap12 formedBilin q y x
  rw [hqy, hxx, hyx] at h
  rw [mul_neg_abstract, hqx, hyq, neg_mul_abstract, mul_neg_abstract,
    hxx, hyy] at h
  have hq : q * q = -1 := by
    abel_nf at h
    exact eq_neg_of_add_eq_zero_right h
  exact hq

@[simp] theorem realization_scalar (r : ℝ) :
    realization (scalar r) = r • (1 : ZornMatrix) := by
  unfold realization scalar Kingdon.Algebra.liftOfLinear
  rw [Kingdon.Algebra.lift_mk]
  simp [Kingdon.Algebra.ambientLift, InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.smul]

noncomputable def scale (r : ℝ) (x : AbstractKingdon) : AbstractKingdon := scalar r * x

/-- Products of symmetric generators span the antisymmetric off-diagonal space. -/
noncomputable def anti (v : ThreeSpace) : AbstractKingdon :=
  scale (v 0) (Kingdon.Algebra.ι formedBilin (basisVec 1) *
    Kingdon.Algebra.ι formedBilin (basisVec 2)) +
  scale (v 1) (Kingdon.Algebra.ι formedBilin (basisVec 2) *
    Kingdon.Algebra.ι formedBilin (basisVec 0)) +
  scale (v 2) (Kingdon.Algebra.ι formedBilin (basisVec 0) *
    Kingdon.Algebra.ι formedBilin (basisVec 1))

noncomputable def upper (v : ThreeSpace) : AbstractKingdon :=
  scale ((2 : ℝ)⁻¹) (Kingdon.Algebra.ι formedBilin v - anti v)

noncomputable def lower (v : ThreeSpace) : AbstractKingdon :=
  scale ((2 : ℝ)⁻¹) (Kingdon.Algebra.ι formedBilin v + anti v)

theorem scale_eq_smul (r : ℝ) (x : AbstractKingdon) : scale r x = r • x := by
  exact Kingdon.Algebra.scalar_mul formedBilin r x

@[simp] theorem smul_zero_abstract (r : ℝ) : r • (0 : AbstractKingdon) = 0 := by
  rw [← Kingdon.Algebra.scalar_mul, mul_zero]

theorem scale_mul_scale (r s : ℝ) (x y : AbstractKingdon) :
    scale r x * scale s y = scale (r * s) (x * y) := by
  rw [scale_eq_smul, scale_eq_smul, scale_eq_smul]
  rw [smul_mul_assoc, mul_smul_comm, mul_smul]

theorem scale_add (r : ℝ) (x y : AbstractKingdon) :
    scale r x + scale r y = scale r (x + y) := by
  simp [scale_eq_smul, smul_add]

@[simp] theorem anti_basisVec_zero :
    anti (basisVec 0) = basisGenerator 1 * basisGenerator 2 := by
  simp [anti, basisVec, scale, scalar, basisGenerator]

@[simp] theorem anti_basisVec_one :
    anti (basisVec 1) = basisGenerator 2 * basisGenerator 0 := by
  simp [anti, basisVec, scale, scalar, basisGenerator]

@[simp] theorem anti_basisVec_two :
    anti (basisVec 2) = basisGenerator 0 * basisGenerator 1 := by
  simp [anti, basisVec, scale, scalar, basisGenerator]

@[simp] theorem scalar_add (r s : ℝ) : scalar (r + s) = scalar r + scalar s := by
  simp [scalar, Unitization.inl_add, Kingdon.Algebra.mk_add]

theorem scale_coeff_add (r s : ℝ) (x : AbstractKingdon) :
    scale (r + s) x = scale r x + scale s x := by
  simp only [scale, scalar_add, add_mul]

theorem add_smul_abstract (r s : ℝ) (x : AbstractKingdon) :
    (r + s) • x = r • x + s • x := by
  simpa only [scale_eq_smul] using scale_coeff_add r s x

theorem neg_smul_abstract (r : ℝ) (x : AbstractKingdon) :
    (-r) • x = -(r • x) := neg_smul r x

theorem sub_smul_abstract (r s : ℝ) (x : AbstractKingdon) :
    (r - s) • x = r • x - s • x := sub_smul r s x

@[simp] theorem anti_add (u v : ThreeSpace) : anti (u + v) = anti u + anti v := by
  simp only [anti, Pi.add_apply, scale_coeff_add]
  abel

@[simp] theorem upper_add (u v : ThreeSpace) : upper (u + v) = upper u + upper v := by
  simp only [upper, Kingdon.Algebra.ι_add, anti_add]
  calc
    scale (2 : ℝ)⁻¹
        (Kingdon.Algebra.ι formedBilin u + Kingdon.Algebra.ι formedBilin v -
          (anti u + anti v)) =
      scale (2 : ℝ)⁻¹
        ((Kingdon.Algebra.ι formedBilin u - anti u) +
          (Kingdon.Algebra.ι formedBilin v - anti v)) := by congr 1 <;> abel
    _ = _ := (scale_add _ _ _).symm

@[simp] theorem lower_add (u v : ThreeSpace) : lower (u + v) = lower u + lower v := by
  simp only [lower, Kingdon.Algebra.ι_add, anti_add]
  calc
    scale (2 : ℝ)⁻¹
        (Kingdon.Algebra.ι formedBilin u + Kingdon.Algebra.ι formedBilin v +
          (anti u + anti v)) =
      scale (2 : ℝ)⁻¹
        ((Kingdon.Algebra.ι formedBilin u + anti u) +
          (Kingdon.Algebra.ι formedBilin v + anti v)) := by congr 1 <;> abel
    _ = _ := (scale_add _ _ _).symm

@[simp] theorem anti_smul (r : ℝ) (v : ThreeSpace) :
    anti (r • v) = r • anti v := by
  simp [anti, Pi.smul_apply, scale_eq_smul, smul_add, smul_eq_mul,
    mul_smul, mul_assoc]

@[simp] theorem upper_smul (r : ℝ) (v : ThreeSpace) :
    upper (r • v) = r • upper v := by
  simp only [upper, Kingdon.Algebra.ι_smul, anti_smul, scale_eq_smul]
  rw [Kingdon.Algebra.scalar_mul]
  simp [smul_sub, smul_smul, mul_comm]

@[simp] theorem lower_smul (r : ℝ) (v : ThreeSpace) :
    lower (r • v) = r • lower v := by
  simp only [lower, Kingdon.Algebra.ι_smul, anti_smul, scale_eq_smul]
  rw [Kingdon.Algebra.scalar_mul]
  simp [smul_add, smul_smul, mul_comm]

theorem smul_scalar (r s : ℝ) :
    r • scalar s = scalar (r * s) := by
  rw [scalar_eq_smul_one, smul_smul, ← scalar_eq_smul_one]

theorem smul_upper (r : ℝ) (v : ThreeSpace) :
    r • upper v = upper (r • v) := by
  simpa using (upper_smul r v).symm

theorem smul_lower (r : ℝ) (v : ThreeSpace) :
    r • lower v = lower (r • v) := by
  simpa using (lower_smul r v).symm

theorem upper_eq_basis_sum (v : ThreeSpace) :
    upper v =
      v 0 • upper (basisVec 0) + v 1 • upper (basisVec 1) +
        v 2 • upper (basisVec 2) := by
  calc
    upper v = upper
        (v 0 • basisVec 0 + v 1 • basisVec 1 + v 2 • basisVec 2) := by
      rw [← threeSpace_eq_basis_sum v]
    _ = _ := by rw [upper_add, upper_add, upper_smul, upper_smul, upper_smul]

theorem lower_eq_basis_sum (v : ThreeSpace) :
    lower v =
      v 0 • lower (basisVec 0) + v 1 • lower (basisVec 1) +
        v 2 • lower (basisVec 2) := by
  calc
    lower v = lower
        (v 0 • basisVec 0 + v 1 • basisVec 1 + v 2 • basisVec 2) := by
      rw [← threeSpace_eq_basis_sum v]
    _ = _ := by rw [lower_add, lower_add, lower_smul, lower_smul, lower_smul]

theorem upper_add_lower (v : ThreeSpace) :
    upper v + lower v = Kingdon.Algebra.ι formedBilin v := by
  simp only [upper, lower, scale, scalar]
  rw [Kingdon.Algebra.scalar_mul, Kingdon.Algebra.scalar_mul, smul_sub, smul_add]
  calc
    (2 : ℝ)⁻¹ • Kingdon.Algebra.ι formedBilin v - (2 : ℝ)⁻¹ • anti v +
        ((2 : ℝ)⁻¹ • Kingdon.Algebra.ι formedBilin v + (2 : ℝ)⁻¹ • anti v) =
      ((2 : ℝ)⁻¹ • Kingdon.Algebra.ι formedBilin v +
        (2 : ℝ)⁻¹ • Kingdon.Algebra.ι formedBilin v) := by abel
    _ = Kingdon.Algebra.ι formedBilin
        (((2 : ℝ)⁻¹ • v) + ((2 : ℝ)⁻¹ • v)) := by
      rw [Kingdon.Algebra.ι_add, Kingdon.Algebra.ι_smul,
        Kingdon.Algebra.scalar_mul]
    _ = Kingdon.Algebra.ι formedBilin v := by
      congr 1
      ext i
      simp
      ring

@[simp] theorem realization_upper (v : ThreeSpace) :
    realization (upper v) = ⟨0, 0, v, 0⟩ := by
  ext <;> simp [upper, anti, scale, basisVec, generator,
    InfoGeometry.Physics.ZornMatrixSU3.mul, InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.neg, InfoGeometry.Physics.ZornMatrixSU3.smul,
    Physics.ZornMatrixSU3.dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> try ring
  all_goals rename_i i; fin_cases i <;> norm_num <;> try rfl <;> ring

@[simp] theorem realization_lower (v : ThreeSpace) :
    realization (lower v) = ⟨0, 0, 0, v⟩ := by
  ext <;> simp [lower, anti, scale, basisVec, generator,
    InfoGeometry.Physics.ZornMatrixSU3.mul, InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.neg, InfoGeometry.Physics.ZornMatrixSU3.smul,
    Physics.ZornMatrixSU3.dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> try ring
  all_goals rename_i i; fin_cases i <;> norm_num <;> try rfl <;> ring

noncomputable def diagonalUpper : AbstractKingdon := upper (basisVec 0) * lower (basisVec 0)

noncomputable def diagonalLower : AbstractKingdon := lower (basisVec 0) * upper (basisVec 0)

theorem diagonalUpper_add_diagonalLower : diagonalUpper + diagonalLower = 1 := by
  let e := basisGenerator 0
  let q := basisGenerator 1 * basisGenerator 2
  have he : e * e = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hraw :
      (e - q) * (e + q) + (e + q) * (e - q) = (4 : ℝ) • (1 : AbstractKingdon) := by
    simp only [sub_mul, add_mul, mul_add, mul_sub]
    rw [he, hq]
    norm_num
    abel_nf
    exact (Nat.cast_smul_eq_nsmul ℝ 4 (1 : AbstractKingdon)).symm
  simp only [diagonalUpper, diagonalLower, upper, lower, anti_basisVec_zero,
    basisGenerator, e, q]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  rw [scale_add]
  change scale (1 / 4) ((e - q) * (e + q) + (e + q) * (e - q)) = 1
  rw [hraw, scale_eq_smul, ← mul_smul]
  norm_num

theorem basisBivector_anticomm_third {i j k : Fin 3} (hij : i ≠ j) :
    (basisGenerator i * basisGenerator j) * basisGenerator k =
      -(basisGenerator k * (basisGenerator i * basisGenerator j)) := by
  have h := Kingdon.Algebra.antiassociate formedBilin (basisVec i) (basisVec j) (basisVec k)
  change (basisGenerator i * basisGenerator j) * basisGenerator k =
    basisGenerator k * (basisGenerator j * basisGenerator i) at h
  rw [basisGenerator_anticomm hij.symm, mul_neg_abstract] at h
  exact h

theorem basisBivector_mul_right (i j : Fin 3) :
    (basisGenerator i * basisGenerator j) * basisGenerator j = basisGenerator i := by
  rw [Kingdon.Algebra.alternative_right formedBilin, basisGenerator_sq, mul_one]

theorem basisGenerator_mul_leftBivector (i j : Fin 3) :
    basisGenerator i * (basisGenerator i * basisGenerator j) = basisGenerator j := by
  rw [← Kingdon.Algebra.alternative_left formedBilin, basisGenerator_sq, one_mul]

theorem basisBivector_mul_left {i j : Fin 3} (hij : i ≠ j) :
    (basisGenerator i * basisGenerator j) * basisGenerator i = -basisGenerator j := by
  rw [Kingdon.Algebra.flexible formedBilin,
    basisGenerator_anticomm hij.symm, mul_neg_abstract,
    ← Kingdon.Algebra.alternative_left formedBilin, basisGenerator_sq, one_mul]

theorem basisGenerator_mul_rightBivector {i j : Fin 3} (hij : i ≠ j) :
    basisGenerator i * (basisGenerator j * basisGenerator i) = -basisGenerator j := by
  rw [basisGenerator_anticomm hij.symm, mul_neg_abstract,
    ← Kingdon.Algebra.alternative_left formedBilin, basisGenerator_sq, one_mul]

theorem basisGenerator_mul_bivector_swap {i j k : Fin 3} (hij : i ≠ j) :
    basisGenerator i * (basisGenerator j * basisGenerator k) =
      -(basisGenerator j * (basisGenerator i * basisGenerator k)) := by
  let a := basisGenerator i
  let b := basisGenerator j
  let c := basisGenerator k
  have hba : b * a = -(a * b) := basisGenerator_anticomm hij.symm
  have h₁ : (a * b) * c = c * (b * a) := by
    exact Kingdon.Algebra.antiassociate formedBilin (basisVec i) (basisVec j) (basisVec k)
  have h₂ : (b * a) * c = c * (a * b) := by
    exact Kingdon.Algebra.antiassociate formedBilin (basisVec j) (basisVec i) (basisVec k)
  have hs := Kingdon.Algebra.associator_swap12 formedBilin a b c
  rw [h₁, h₂, hba, mul_neg_abstract] at hs
  abel_nf at hs
  have hs' : -(c * (a * b)) + -(a * (b * c)) =
      -(c * (a * b)) + b * (a * c) := by
    simpa only [neg_one_smul] using hs
  have hh : -(a * (b * c)) = b * (a * c) := add_left_cancel hs'
  calc
    a * (b * c) = -(-(a * (b * c))) := by simp
    _ = -(b * (a * c)) := by rw [hh]

theorem basisTrivector_mul_middle {i j k : Fin 3} (hij : i ≠ j) :
    (basisGenerator i * (basisGenerator j * basisGenerator k)) * basisGenerator j =
      -(basisGenerator k * basisGenerator i) := by
  have h₃ :
      (basisGenerator i * basisGenerator k) * basisGenerator j =
        basisGenerator j * (basisGenerator k * basisGenerator i) := by
    exact Kingdon.Algebra.antiassociate formedBilin (basisVec i) (basisVec k) (basisVec j)
  calc
    (basisGenerator i * (basisGenerator j * basisGenerator k)) * basisGenerator j =
        (-(basisGenerator j * (basisGenerator i * basisGenerator k))) *
          basisGenerator j := by rw [basisGenerator_mul_bivector_swap hij]
    _ = -((basisGenerator j * (basisGenerator i * basisGenerator k)) *
          basisGenerator j) := neg_mul_abstract _ _
    _ = -(basisGenerator j *
          ((basisGenerator i * basisGenerator k) * basisGenerator j)) := by
      rw [Kingdon.Algebra.flexible formedBilin]
    _ = -(basisGenerator j *
          (basisGenerator j * (basisGenerator k * basisGenerator i))) := by rw [h₃]
    _ = -((basisGenerator j * basisGenerator j) *
          (basisGenerator k * basisGenerator i)) := by
      rw [Kingdon.Algebra.alternative_left formedBilin]
    _ = -(basisGenerator k * basisGenerator i) := by rw [basisGenerator_sq, one_mul]

theorem basisTrivector_mul_bivector {i j k : Fin 3} (hij : i ≠ j) :
    (basisGenerator i * (basisGenerator j * basisGenerator k)) *
        (basisGenerator k * basisGenerator i) =
      -basisGenerator j := by
  rw [Kingdon.Algebra.middle_moufang]
  rw [basisBivector_mul_right]
  exact basisGenerator_mul_rightBivector hij

theorem basisBivector_chain_forward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator i * basisGenerator j) *
        (basisGenerator j * basisGenerator k) =
      -(basisGenerator i * basisGenerator k) := by
  rw [basisGenerator_anticomm hij,
    basisGenerator_anticomm hjk]
  rw [neg_mul_abstract, mul_neg_abstract, neg_neg]
  rw [Kingdon.Algebra.middle_moufang]
  rw [basisBivector_anticomm_third hik,
    mul_neg_abstract,
    ← Kingdon.Algebra.alternative_left formedBilin,
    basisGenerator_sq, one_mul]

theorem basisBivector_chain_reverse {i j k : Fin 3} (hki : k ≠ i) :
    (basisGenerator j * basisGenerator k) *
        (basisGenerator i * basisGenerator j) =
      basisGenerator i * basisGenerator k := by
  rw [Kingdon.Algebra.middle_moufang]
  rw [basisBivector_anticomm_third hki,
    mul_neg_abstract,
    ← Kingdon.Algebra.alternative_left formedBilin,
    basisGenerator_sq, one_mul,
    basisGenerator_anticomm hki, neg_neg]

theorem distinguished_bivector_anticomm :
    (basisGenerator 1 * basisGenerator 2) * basisGenerator 0 =
      -(basisGenerator 0 * (basisGenerator 1 * basisGenerator 2)) :=
  basisBivector_anticomm_third (by decide : (1 : Fin 3) ≠ 2)

@[simp] theorem upper_basisVec_zero_sq : upper (basisVec 0) * upper (basisVec 0) = 0 := by
  let e := basisGenerator 0
  let q := basisGenerator 1 * basisGenerator 2
  have he : e * e = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqe : q * e = -(e * q) := distinguished_bivector_anticomm
  have hraw : (e - q) * (e - q) = 0 := by
    simp only [mul_sub, sub_mul]
    rw [he, hq, hqe]
    abel
  simp only [upper, anti_basisVec_zero, basisGenerator, e, q]
  rw [scale_mul_scale]
  change scale ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) ((e - q) * (e - q)) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem lower_basisVec_zero_sq : lower (basisVec 0) * lower (basisVec 0) = 0 := by
  let e := basisGenerator 0
  let q := basisGenerator 1 * basisGenerator 2
  have he : e * e = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqe : q * e = -(e * q) := distinguished_bivector_anticomm
  have hraw : (e + q) * (e + q) = 0 := by
    simp only [mul_add, add_mul]
    rw [he, hq, hqe]
    abel
  simp only [lower, anti_basisVec_zero, basisGenerator, e, q]
  rw [scale_mul_scale]
  change scale ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) ((e + q) * (e + q)) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem diagonalUpper_mul_diagonalLower :
    diagonalUpper * diagonalLower = 0 := by
  unfold diagonalUpper diagonalLower
  rw [Kingdon.Algebra.middle_moufang, lower_basisVec_zero_sq, zero_mul, mul_zero]

@[simp] theorem diagonalLower_mul_diagonalUpper :
    diagonalLower * diagonalUpper = 0 := by
  unfold diagonalLower diagonalUpper
  rw [Kingdon.Algebra.middle_moufang, upper_basisVec_zero_sq, zero_mul, mul_zero]

@[simp] theorem diagonalUpper_sq : diagonalUpper * diagonalUpper = diagonalUpper := by
  have h := congrArg (fun a : AbstractKingdon => diagonalUpper * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, diagonalUpper_mul_diagonalLower, add_zero, mul_one] at h
  exact h

@[simp] theorem diagonalLower_sq : diagonalLower * diagonalLower = diagonalLower := by
  have h := congrArg (fun a : AbstractKingdon => diagonalLower * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, diagonalLower_mul_diagonalUpper, zero_add, mul_one] at h
  exact h


theorem upperRawProductForward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator i - basisGenerator j * basisGenerator k) *
      (basisGenerator j - basisGenerator k * basisGenerator i) =
      (basisGenerator i * basisGenerator j + basisGenerator k) +
        (basisGenerator i * basisGenerator j + basisGenerator k) := by
  simp only [mul_sub, sub_mul]
  rw [basisGenerator_mul_rightBivector hik,
    basisBivector_mul_left hjk,
    basisBivector_chain_forward hjk hik.symm hij.symm]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem upperRawProductReverse {i j k : Fin 3}
    (hij : i ≠ j) (_hjk : j ≠ k) (_hik : i ≠ k) :
    (basisGenerator j - basisGenerator k * basisGenerator i) *
      (basisGenerator i - basisGenerator j * basisGenerator k) =
      (-basisGenerator k - basisGenerator i * basisGenerator j) +
        (-basisGenerator k - basisGenerator i * basisGenerator j) := by
  simp only [mul_sub, sub_mul]
  rw [basisGenerator_anticomm hij.symm]
  rw [basisBivector_mul_right, basisGenerator_mul_leftBivector]
  rw [basisBivector_chain_reverse (i := j) (j := k) (k := i) hij]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem upperBasisProductForward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i)
    (hak : anti (basisVec k) = basisGenerator i * basisGenerator j) :
    upper (basisVec i) * upper (basisVec j) = lower (basisVec k) := by
  simp only [upper, lower, hai, haj, hak]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
      ((basisGenerator i - basisGenerator j * basisGenerator k) *
       (basisGenerator j - basisGenerator k * basisGenerator i)) =
    scale 2⁻¹ (basisGenerator k + basisGenerator i * basisGenerator j)
  rw [upperRawProductForward hij hjk hik]
  rw [scale_eq_smul, scale_eq_smul]
  rw [smul_add, ← add_smul]
  norm_num
  abel

theorem upperBasisProductReverse {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i)
    (hak : anti (basisVec k) = basisGenerator i * basisGenerator j) :
    upper (basisVec j) * upper (basisVec i) = -lower (basisVec k) := by
  simp only [upper, lower, hai, haj, hak]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
      ((basisGenerator j - basisGenerator k * basisGenerator i) *
       (basisGenerator i - basisGenerator j * basisGenerator k)) =
    -scale 2⁻¹ (basisGenerator k + basisGenerator i * basisGenerator j)
  rw [upperRawProductReverse hij hjk hik]
  rw [scale_eq_smul, scale_eq_smul]
  conv_rhs => rw [← neg_one_smul ℝ, smul_smul]
  rw [smul_add, ← add_smul]
  norm_num
  rw [smul_sub, smul_neg]
  abel

theorem upperRawSquare {i j k : Fin 3} (hjk : j ≠ k) :
    (basisGenerator i - basisGenerator j * basisGenerator k) *
      (basisGenerator i - basisGenerator j * basisGenerator k) = 0 := by
  simp only [mul_sub, sub_mul]
  rw [basisGenerator_sq, basisBivector_sq hjk,
    basisBivector_anticomm_third hjk]
  abel

theorem upperBasisSquareOfAnti {i j k : Fin 3} (hjk : j ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k) :
    upper (basisVec i) * upper (basisVec i) = 0 := by
  simp only [upper, hai]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
      ((basisGenerator i - basisGenerator j * basisGenerator k) *
       (basisGenerator i - basisGenerator j * basisGenerator k)) = 0
  rw [upperRawSquare hjk]
  simp [scale]

@[simp] theorem upper_basisVec_one_sq :
    upper (basisVec 1) * upper (basisVec 1) = 0 := by
  exact upperBasisSquareOfAnti (by decide) anti_basisVec_one

@[simp] theorem upper_basisVec_two_sq :
    upper (basisVec 2) * upper (basisVec 2) = 0 := by
  exact upperBasisSquareOfAnti (by decide) anti_basisVec_two

@[simp] theorem upper_basisVec_zero_mul_one :
    upper (basisVec 0) * upper (basisVec 1) = lower (basisVec 2) := by
  exact upperBasisProductForward (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one anti_basisVec_two

@[simp] theorem upper_basisVec_one_mul_zero :
    upper (basisVec 1) * upper (basisVec 0) = -lower (basisVec 2) := by
  exact upperBasisProductReverse (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one anti_basisVec_two

@[simp] theorem upper_basisVec_one_mul_two :
    upper (basisVec 1) * upper (basisVec 2) = lower (basisVec 0) := by
  exact upperBasisProductForward (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two anti_basisVec_zero

@[simp] theorem upper_basisVec_two_mul_one :
    upper (basisVec 2) * upper (basisVec 1) = -lower (basisVec 0) := by
  exact upperBasisProductReverse (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two anti_basisVec_zero

@[simp] theorem upper_basisVec_two_mul_zero :
    upper (basisVec 2) * upper (basisVec 0) = lower (basisVec 1) := by
  exact upperBasisProductForward (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero anti_basisVec_one

@[simp] theorem upper_basisVec_zero_mul_two :
    upper (basisVec 0) * upper (basisVec 2) = -lower (basisVec 1) := by
  exact upperBasisProductReverse (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero anti_basisVec_one

theorem lowerRawProductForward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator i + basisGenerator j * basisGenerator k) *
      (basisGenerator j + basisGenerator k * basisGenerator i) =
      (basisGenerator i * basisGenerator j - basisGenerator k) +
        (basisGenerator i * basisGenerator j - basisGenerator k) := by
  simp only [mul_add, add_mul]
  rw [basisGenerator_mul_rightBivector hik,
    basisBivector_mul_left hjk,
    basisBivector_chain_forward hjk hik.symm hij.symm]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem lowerRawProductReverse {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator j + basisGenerator k * basisGenerator i) *
      (basisGenerator i + basisGenerator j * basisGenerator k) =
      (basisGenerator k - basisGenerator i * basisGenerator j) +
        (basisGenerator k - basisGenerator i * basisGenerator j) := by
  simp only [mul_add, add_mul]
  rw [basisGenerator_anticomm hij.symm]
  rw [basisBivector_mul_right, basisGenerator_mul_leftBivector]
  rw [basisBivector_chain_reverse (i := j) (j := k) (k := i) hij]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem lowerBasisProductForward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i)
    (hak : anti (basisVec k) = basisGenerator i * basisGenerator j) :
    lower (basisVec i) * lower (basisVec j) = -upper (basisVec k) := by
  simp only [lower, upper, hai, haj, hak]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
      ((basisGenerator i + basisGenerator j * basisGenerator k) *
       (basisGenerator j + basisGenerator k * basisGenerator i)) =
    -scale 2⁻¹ (basisGenerator k - basisGenerator i * basisGenerator j)
  rw [lowerRawProductForward hij hjk hik]
  rw [scale_eq_smul, scale_eq_smul]
  rw [smul_add, ← add_smul]
  norm_num
  simp only [smul_sub]
  abel

theorem lowerBasisProductReverse {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i)
    (hak : anti (basisVec k) = basisGenerator i * basisGenerator j) :
    lower (basisVec j) * lower (basisVec i) = upper (basisVec k) := by
  simp only [lower, upper, hai, haj, hak]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
      ((basisGenerator j + basisGenerator k * basisGenerator i) *
       (basisGenerator i + basisGenerator j * basisGenerator k)) =
    scale 2⁻¹ (basisGenerator k - basisGenerator i * basisGenerator j)
  rw [lowerRawProductReverse hij hjk hik]
  rw [scale_eq_smul, scale_eq_smul]
  rw [smul_add, ← add_smul]
  norm_num

theorem lowerRawSquare {i j k : Fin 3} (hjk : j ≠ k) :
    (basisGenerator i + basisGenerator j * basisGenerator k) *
      (basisGenerator i + basisGenerator j * basisGenerator k) = 0 := by
  simp only [mul_add, add_mul]
  rw [basisGenerator_sq, basisBivector_sq hjk,
    basisBivector_anticomm_third hjk]
  abel

theorem lowerBasisSquareOfAnti {i j k : Fin 3} (hjk : j ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k) :
    lower (basisVec i) * lower (basisVec i) = 0 := by
  simp only [lower, hai]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
      ((basisGenerator i + basisGenerator j * basisGenerator k) *
       (basisGenerator i + basisGenerator j * basisGenerator k)) = 0
  rw [lowerRawSquare hjk]
  simp [scale]

@[simp] theorem lower_basisVec_one_sq :
    lower (basisVec 1) * lower (basisVec 1) = 0 := by
  exact lowerBasisSquareOfAnti (by decide) anti_basisVec_one

@[simp] theorem lower_basisVec_two_sq :
    lower (basisVec 2) * lower (basisVec 2) = 0 := by
  exact lowerBasisSquareOfAnti (by decide) anti_basisVec_two

@[simp] theorem lower_basisVec_zero_mul_one :
    lower (basisVec 0) * lower (basisVec 1) = -upper (basisVec 2) := by
  exact lowerBasisProductForward (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one anti_basisVec_two

@[simp] theorem lower_basisVec_one_mul_zero :
    lower (basisVec 1) * lower (basisVec 0) = upper (basisVec 2) := by
  exact lowerBasisProductReverse (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one anti_basisVec_two

@[simp] theorem lower_basisVec_one_mul_two :
    lower (basisVec 1) * lower (basisVec 2) = -upper (basisVec 0) := by
  exact lowerBasisProductForward (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two anti_basisVec_zero

@[simp] theorem lower_basisVec_two_mul_one :
    lower (basisVec 2) * lower (basisVec 1) = upper (basisVec 0) := by
  exact lowerBasisProductReverse (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two anti_basisVec_zero

@[simp] theorem lower_basisVec_two_mul_zero :
    lower (basisVec 2) * lower (basisVec 0) = -upper (basisVec 1) := by
  exact lowerBasisProductForward (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero anti_basisVec_one

@[simp] theorem lower_basisVec_zero_mul_two :
    lower (basisVec 0) * lower (basisVec 2) = upper (basisVec 1) := by
  exact lowerBasisProductReverse (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero anti_basisVec_one

@[simp] theorem upper_basisVec_zero_mul_diagonalUpper :
    upper (basisVec 0) * diagonalUpper = 0 := by
  unfold diagonalUpper
  rw [← Kingdon.Algebra.alternative_left formedBilin,
    upper_basisVec_zero_sq, zero_mul]

@[simp] theorem upper_basisVec_one_mul_diagonalUpper :
    upper (basisVec 1) * diagonalUpper = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := c * a
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have hbt : b * t = r := by
    rw [show t = -(b * (a * c)) by
      simpa [a, b, c, q, t] using
        (basisGenerator_mul_bivector_swap
          (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))]
    rw [mul_neg_abstract, ← Kingdon.Algebra.alternative_left,
      basisGenerator_sq, one_mul]
    rw [show -(a * c) = r by
      rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2)]
      simp [a, c, r]]
  have htbr : t = b * r := by
    calc
      t = -(b * (a * c)) := by
        simpa [a, b, c, q, t] using
          (basisGenerator_mul_bivector_swap
            (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))
      _ = b * r := by
        rw [show a * c = -r by
          rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2)],
          mul_neg_abstract, neg_neg]
  have htbiv : t * r = -b := by
    simpa [a, b, c, r, t, q] using
      (basisTrivector_mul_bivector
        (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))
  have hrb : r * b = -t := by
    calc
      r * b = b * (a * c) := by
        simpa [a, b, c, r] using
          (Kingdon.Algebra.antiassociate formedBilin
            (basisVec 2) (basisVec 0) (basisVec 1))
      _ = -t := by
        rw [show a * c = -r by
          rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2)],
          mul_neg_abstract, ← htbr]
  have hrt : r * t = b := by
    rw [htbr, ← Kingdon.Algebra.flexible, hrb,
      neg_mul_abstract, htbiv, neg_neg]
  have hright : (a - q) * (a + q) = (1 + t) + (1 + t) := by
    simp only [sub_mul, mul_add]
    rw [ha, hq, hqa]
    abel
  have hinner : (b - r) * (1 + t) = 0 := by
    simp only [mul_add, mul_one, sub_mul]
    rw [hbt, hrt]
    abel
  have hraw : (b - r) * ((a - q) * (a + q)) = 0 := by
    rw [hright, mul_add, hinner, add_zero]
  unfold diagonalUpper
  simp only [upper, lower, anti_basisVec_zero, anti_basisVec_one]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) ((b - r) * ((a - q) * (a + q))) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem upper_basisVec_two_mul_diagonalUpper :
    upper (basisVec 2) * diagonalUpper = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := a * b
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have hct : c * t = r := by
    rw [show t = -(b * (a * c)) by
      simpa [a, b, c, q, t] using
        (basisGenerator_mul_bivector_swap
          (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))]
    rw [mul_neg_abstract]
    have hbac : b * (a * c) = -(b * (c * a)) := by
      rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2), mul_neg_abstract]
    rw [hbac, mul_neg_abstract, neg_neg]
    rw [← Kingdon.Algebra.left_moufang]
    rw [Kingdon.Algebra.flexible formedBilin]
    rw [basisGenerator_mul_rightBivector (by decide : (2 : Fin 3) ≠ 1)]
    rw [neg_mul_abstract,
      basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 0), neg_neg]
  have hrt : r * t = c := by
    have hm := Kingdon.Algebra.middle_moufang formedBilin a b (-q)
    rw [neg_mul_abstract, hqa, neg_neg] at hm
    rw [hm]
    rw [mul_neg_abstract]
    rw [← Kingdon.Algebra.alternative_left formedBilin,
      basisGenerator_sq, one_mul]
    rw [neg_mul_abstract]
    rw [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 0), mul_neg_abstract]
    change -(a * -(a * c)) = c
    simp only [mul_neg_abstract, neg_neg]
    rw [← Kingdon.Algebra.alternative_left formedBilin,
      basisGenerator_sq, one_mul]
  have hright : (a - q) * (a + q) = (1 + t) + (1 + t) := by
    simp only [sub_mul, mul_add]
    rw [ha, hq, hqa]
    abel
  have hinner : (c - r) * (1 + t) = 0 := by
    simp only [mul_add, mul_one, sub_mul]
    rw [hct, hrt]
    abel
  have hraw : (c - r) * ((a - q) * (a + q)) = 0 := by
    rw [hright, mul_add, hinner, add_zero]
  unfold diagonalUpper
  simp only [upper, lower, anti_basisVec_zero, anti_basisVec_two]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) ((c - r) * ((a - q) * (a + q))) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem diagonalLower_mul_upper_basisVec_zero :
    diagonalLower * upper (basisVec 0) = 0 := by
  unfold diagonalLower
  rw [Kingdon.Algebra.alternative_right formedBilin,
    upper_basisVec_zero_sq, mul_zero]

@[simp] theorem diagonalLower_mul_upper_basisVec_one :
    diagonalLower * upper (basisVec 1) = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := c * a
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have htb : t * b = -r := by
    simpa [a, b, c, r, t, q] using
      (basisTrivector_mul_middle (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))
  have htr : t * r = -b := by
    simpa [a, b, c, r, t, q] using
      (basisTrivector_mul_bivector (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))
  have hleft : (a + q) * (a - q) = (1 - t) + (1 - t) := by
    simp only [add_mul, mul_sub, sub_eq_add_neg, mul_add]
    rw [mul_neg_abstract, mul_neg_abstract, ha, hq, hqa, neg_neg]
    abel
  have hinner : (1 - t) * (b - r) = 0 := by
    simp only [sub_mul, one_mul, mul_sub]
    rw [htb, htr]
    abel
  have hraw : ((a + q) * (a - q)) * (b - r) = 0 := by
    rw [hleft, add_mul, hinner, add_zero]
  unfold diagonalLower
  simp only [lower, upper, anti_basisVec_zero, anti_basisVec_one]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) (((a + q) * (a - q)) * (b - r)) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem diagonalLower_mul_upper_basisVec_two :
    diagonalLower * upper (basisVec 2) = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := a * b
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have htc : t * c = -r := by
    have h := basisTrivector_mul_middle
      (i := (0 : Fin 3)) (j := 2) (k := 1) (by decide)
    rw [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 1),
      mul_neg_abstract, neg_mul_abstract,
      basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 0), neg_neg] at h
    have hn := congrArg (fun x : AbstractKingdon => -x) h
    simpa [a, b, c, q, r, t] using hn
  have htr : t * r = -c := by
    have h := basisTrivector_mul_bivector
      (i := (0 : Fin 3)) (j := 2) (k := 1) (by decide)
    rw [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 1),
      mul_neg_abstract,
      basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 0),
      neg_mul_abstract, mul_neg_abstract, neg_neg] at h
    simpa [a, b, c, q, r, t] using h
  have hleft : (a + q) * (a - q) = (1 - t) + (1 - t) := by
    simp only [add_mul, mul_sub, sub_eq_add_neg, mul_add]
    rw [mul_neg_abstract, mul_neg_abstract, ha, hq, hqa, neg_neg]
    abel
  have hinner : (1 - t) * (c - r) = 0 := by
    simp only [sub_mul, one_mul, mul_sub]
    rw [htc, htr]
    abel
  have hraw : ((a + q) * (a - q)) * (c - r) = 0 := by
    rw [hleft, add_mul, hinner, add_zero]
  unfold diagonalLower
  simp only [lower, upper, anti_basisVec_zero, anti_basisVec_two]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) (((a + q) * (a - q)) * (c - r)) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem diagonalUpper_mul_upper_basisVec_zero :
    diagonalUpper * upper (basisVec 0) = upper (basisVec 0) := by
  have h := congrArg (fun a : AbstractKingdon => a * upper (basisVec 0))
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [add_mul, diagonalLower_mul_upper_basisVec_zero, add_zero, one_mul] at h
  exact h

@[simp] theorem diagonalUpper_mul_upper_basisVec_one :
    diagonalUpper * upper (basisVec 1) = upper (basisVec 1) := by
  have h := congrArg (fun a : AbstractKingdon => a * upper (basisVec 1))
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [add_mul, diagonalLower_mul_upper_basisVec_one, add_zero, one_mul] at h
  exact h

@[simp] theorem diagonalUpper_mul_upper_basisVec_two :
    diagonalUpper * upper (basisVec 2) = upper (basisVec 2) := by
  have h := congrArg (fun a : AbstractKingdon => a * upper (basisVec 2))
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [add_mul, diagonalLower_mul_upper_basisVec_two, add_zero, one_mul] at h
  exact h

@[simp] theorem upper_basisVec_zero_mul_diagonalLower :
    upper (basisVec 0) * diagonalLower = upper (basisVec 0) := by
  have h := congrArg (fun a : AbstractKingdon => upper (basisVec 0) * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, upper_basisVec_zero_mul_diagonalUpper, zero_add, mul_one] at h
  exact h

@[simp] theorem upper_basisVec_one_mul_diagonalLower :
    upper (basisVec 1) * diagonalLower = upper (basisVec 1) := by
  have h := congrArg (fun a : AbstractKingdon => upper (basisVec 1) * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, upper_basisVec_one_mul_diagonalUpper, zero_add, mul_one] at h
  exact h

@[simp] theorem upper_basisVec_two_mul_diagonalLower :
    upper (basisVec 2) * diagonalLower = upper (basisVec 2) := by
  have h := congrArg (fun a : AbstractKingdon => upper (basisVec 2) * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, upper_basisVec_two_mul_diagonalUpper, zero_add, mul_one] at h
  exact h

@[simp] theorem diagonalUpper_mul_lower_basisVec_zero :
    diagonalUpper * lower (basisVec 0) = 0 := by
  unfold diagonalUpper
  rw [Kingdon.Algebra.alternative_right formedBilin,
    lower_basisVec_zero_sq, mul_zero]

@[simp] theorem diagonalUpper_mul_lower_basisVec_one :
    diagonalUpper * lower (basisVec 1) = 0 := by
  let e := basisGenerator 0
  let a := basisGenerator 1
  let b := basisGenerator 2
  let q := a * b
  have he : e * e = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqe : q * e = -(e * q) := distinguished_bivector_anticomm
  have hP : (e - q) * (e + q) = (2 : ℝ) • (1 + e * q) := by
    simp only [mul_add, sub_mul]
    rw [he, hq, hqe]
    norm_num
    simp only [smul_add, two_smul]
    abel
  have htriv_a : (e * q) * a = -(b * e) := by
    exact basisTrivector_mul_middle (i := 0) (j := 1) (k := 2) (by decide)
  have htriv_be : (e * q) * (b * e) = -a := by
    exact basisTrivector_mul_bivector (i := 0) (j := 1) (k := 2) (by decide)
  have hzero : (1 + e * q) * (a + b * e) = 0 := by
    rw [add_mul, one_mul, mul_add, htriv_a, htriv_be]
    abel
  simp only [diagonalUpper, upper, lower, anti_basisVec_zero,
    anti_basisVec_one, basisGenerator, e, a, b, q]
  rw [scale_mul_scale, scale_mul_scale]
  change scale (((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) * (2 : ℝ)⁻¹)
    (((e - q) * (e + q)) * (a + b * e)) = 0
  rw [hP, smul_mul_assoc, hzero]
  have hz : (2 : ℝ) • (0 : AbstractKingdon) = 0 := by
    rw [← Kingdon.Algebra.scalar_mul, mul_zero]
  rw [hz]
  simp [scale]

@[simp] theorem diagonalUpper_mul_lower_basisVec_two :
    diagonalUpper * lower (basisVec 2) = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := a * b
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have htc : t * c = -r := by
    have h := basisTrivector_mul_middle
      (i := (0 : Fin 3)) (j := 2) (k := 1) (by decide)
    rw [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 1),
      mul_neg_abstract, neg_mul_abstract,
      basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 0), neg_neg] at h
    have hn := congrArg (fun x : AbstractKingdon => -x) h
    simpa [a, b, c, q, r, t] using hn
  have htr : t * r = -c := by
    have h := basisTrivector_mul_bivector
      (i := (0 : Fin 3)) (j := 2) (k := 1) (by decide)
    rw [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 1),
      mul_neg_abstract,
      basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 0),
      neg_mul_abstract, mul_neg_abstract, neg_neg] at h
    simpa [a, b, c, q, r, t] using h
  have hright : (a - q) * (a + q) = (1 + t) + (1 + t) := by
    simp only [sub_mul, mul_add]
    rw [ha, hq, hqa]
    abel
  have hinner : (1 + t) * (c + r) = 0 := by
    simp only [add_mul, one_mul, mul_add]
    rw [htc, htr]
    abel
  have hraw : ((a - q) * (a + q)) * (c + r) = 0 := by
    rw [hright, add_mul, hinner, add_zero]
  unfold diagonalUpper
  simp only [upper, lower, anti_basisVec_zero, anti_basisVec_two]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) (((a - q) * (a + q)) * (c + r)) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem lower_basisVec_zero_mul_diagonalLower :
    lower (basisVec 0) * diagonalLower = 0 := by
  unfold diagonalLower
  rw [← Kingdon.Algebra.alternative_left formedBilin,
    lower_basisVec_zero_sq, zero_mul]

@[simp] theorem lower_basisVec_one_mul_diagonalLower :
    lower (basisVec 1) * diagonalLower = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := c * a
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have hbt : b * t = r := by
    rw [show t = -(b * (a * c)) by
      simpa [a, b, c, q, t] using
        (basisGenerator_mul_bivector_swap
          (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))]
    rw [mul_neg_abstract, ← Kingdon.Algebra.alternative_left,
      basisGenerator_sq, one_mul]
    rw [show -(a * c) = r by
      rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2)]
      simp [a, c, r]]
  have htbr : t = b * r := by
    calc
      t = -(b * (a * c)) := by
        simpa [a, b, c, q, t] using
          (basisGenerator_mul_bivector_swap
            (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))
      _ = b * r := by
        rw [show a * c = -r by
          rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2)],
          mul_neg_abstract, neg_neg]
  have htbiv : t * r = -b := by
    simpa [a, b, c, r, t, q] using
      (basisTrivector_mul_bivector
        (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))
  have hrb : r * b = -t := by
    calc
      r * b = b * (a * c) := by
        simpa [a, b, c, r] using
          (Kingdon.Algebra.antiassociate formedBilin
            (basisVec 2) (basisVec 0) (basisVec 1))
      _ = -t := by
        rw [show a * c = -r by
          rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2)],
          mul_neg_abstract, ← htbr]
  have hrt : r * t = b := by
    rw [htbr, ← Kingdon.Algebra.flexible, hrb,
      neg_mul_abstract, htbiv, neg_neg]
  have hright : (a + q) * (a - q) = (1 - t) + (1 - t) := by
    simp only [add_mul, sub_eq_add_neg, mul_add]
    rw [mul_neg_abstract, mul_neg_abstract, ha, hq, hqa, neg_neg]
    abel
  have hinner : (b + r) * (1 - t) = 0 := by
    simp only [mul_sub, mul_one, add_mul]
    rw [hbt, hrt]
    abel
  have hraw : (b + r) * ((a + q) * (a - q)) = 0 := by
    rw [hright, mul_add, hinner, add_zero]
  unfold diagonalLower
  simp only [lower, upper, anti_basisVec_zero, anti_basisVec_one]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) ((b + r) * ((a + q) * (a - q))) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem lower_basisVec_two_mul_diagonalLower :
    lower (basisVec 2) * diagonalLower = 0 := by
  let a := basisGenerator 0
  let b := basisGenerator 1
  let c := basisGenerator 2
  let q := b * c
  let r := a * b
  let t := a * q
  have ha : a * a = 1 := basisGenerator_sq 0
  have hq : q * q = -1 := basisBivector_sq (by decide : (1 : Fin 3) ≠ 2)
  have hqa : q * a = -t := by
    simpa [a, b, c, q, t] using
      (basisBivector_anticomm_third (i := (1 : Fin 3)) (j := 2) (k := 0) (by decide))
  have hct : c * t = r := by
    rw [show t = -(b * (a * c)) by
      simpa [a, b, c, q, t] using
        (basisGenerator_mul_bivector_swap
          (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide))]
    rw [mul_neg_abstract]
    have hbac : b * (a * c) = -(b * (c * a)) := by
      rw [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 2), mul_neg_abstract]
    rw [hbac, mul_neg_abstract, neg_neg]
    rw [← Kingdon.Algebra.left_moufang]
    rw [Kingdon.Algebra.flexible formedBilin]
    rw [basisGenerator_mul_rightBivector (by decide : (2 : Fin 3) ≠ 1)]
    rw [neg_mul_abstract,
      basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 0), neg_neg]
  have hrt : r * t = c := by
    have hm := Kingdon.Algebra.middle_moufang formedBilin a b (-q)
    rw [neg_mul_abstract, hqa, neg_neg] at hm
    rw [hm]
    rw [mul_neg_abstract]
    rw [← Kingdon.Algebra.alternative_left formedBilin,
      basisGenerator_sq, one_mul]
    rw [neg_mul_abstract]
    rw [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 0), mul_neg_abstract]
    change -(a * -(a * c)) = c
    simp only [mul_neg_abstract, neg_neg]
    rw [← Kingdon.Algebra.alternative_left formedBilin,
      basisGenerator_sq, one_mul]
  have hright : (a + q) * (a - q) = (1 - t) + (1 - t) := by
    simp only [add_mul, sub_eq_add_neg, mul_add]
    rw [mul_neg_abstract, mul_neg_abstract, ha, hq, hqa, neg_neg]
    abel
  have hinner : (c + r) * (1 - t) = 0 := by
    simp only [mul_sub, mul_one, add_mul]
    rw [hct, hrt]
    abel
  have hraw : (c + r) * ((a + q) * (a - q)) = 0 := by
    rw [hright, mul_add, hinner, add_zero]
  unfold diagonalLower
  simp only [lower, upper, anti_basisVec_zero, anti_basisVec_two]
  rw [scale_mul_scale, scale_mul_scale]
  norm_num
  change scale (1 / 8) ((c + r) * ((a + q) * (a - q))) = 0
  rw [hraw]
  simp [scale]

@[simp] theorem diagonalLower_mul_lower_basisVec_zero :
    diagonalLower * lower (basisVec 0) = lower (basisVec 0) := by
  have h := congrArg (fun a : AbstractKingdon => a * lower (basisVec 0))
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [add_mul, diagonalUpper_mul_lower_basisVec_zero, zero_add, one_mul] at h
  exact h

@[simp] theorem diagonalLower_mul_lower_basisVec_one :
    diagonalLower * lower (basisVec 1) = lower (basisVec 1) := by
  have h := congrArg (fun a : AbstractKingdon => a * lower (basisVec 1))
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [add_mul, diagonalUpper_mul_lower_basisVec_one, zero_add, one_mul] at h
  exact h

@[simp] theorem diagonalLower_mul_lower_basisVec_two :
    diagonalLower * lower (basisVec 2) = lower (basisVec 2) := by
  have h := congrArg (fun a : AbstractKingdon => a * lower (basisVec 2))
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [add_mul, diagonalUpper_mul_lower_basisVec_two, zero_add, one_mul] at h
  exact h

@[simp] theorem lower_basisVec_zero_mul_diagonalUpper :
    lower (basisVec 0) * diagonalUpper = lower (basisVec 0) := by
  have h := congrArg (fun a : AbstractKingdon => lower (basisVec 0) * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, lower_basisVec_zero_mul_diagonalLower, add_zero, mul_one] at h
  exact h

@[simp] theorem lower_basisVec_one_mul_diagonalUpper :
    lower (basisVec 1) * diagonalUpper = lower (basisVec 1) := by
  have h := congrArg (fun a : AbstractKingdon => lower (basisVec 1) * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, lower_basisVec_one_mul_diagonalLower, add_zero, mul_one] at h
  exact h

@[simp] theorem lower_basisVec_two_mul_diagonalUpper :
    lower (basisVec 2) * diagonalUpper = lower (basisVec 2) := by
  have h := congrArg (fun a : AbstractKingdon => lower (basisVec 2) * a)
    diagonalUpper_add_diagonalLower
  dsimp only at h
  rw [mul_add, lower_basisVec_two_mul_diagonalLower, add_zero, mul_one] at h
  exact h

@[simp] theorem diagonalUpper_mul_upper (v : ThreeSpace) :
    diagonalUpper * upper v = upper v := by
  rw [upper_eq_basis_sum]
  simp [mul_add, mul_smul_comm]

@[simp] theorem diagonalLower_mul_upper (v : ThreeSpace) :
    diagonalLower * upper v = 0 := by
  rw [upper_eq_basis_sum]
  simp [mul_add, mul_smul_comm]

@[simp] theorem upper_mul_diagonalUpper (v : ThreeSpace) :
    upper v * diagonalUpper = 0 := by
  rw [upper_eq_basis_sum]
  simp [add_mul, smul_mul_assoc]

@[simp] theorem upper_mul_diagonalLower (v : ThreeSpace) :
    upper v * diagonalLower = upper v := by
  rw [upper_eq_basis_sum]
  simp [add_mul, smul_mul_assoc]

@[simp] theorem diagonalUpper_mul_lower (v : ThreeSpace) :
    diagonalUpper * lower v = 0 := by
  rw [lower_eq_basis_sum]
  simp [mul_add, mul_smul_comm]

@[simp] theorem diagonalLower_mul_lower (v : ThreeSpace) :
    diagonalLower * lower v = lower v := by
  rw [lower_eq_basis_sum]
  simp [mul_add, mul_smul_comm]

@[simp] theorem lower_mul_diagonalUpper (v : ThreeSpace) :
    lower v * diagonalUpper = lower v := by
  rw [lower_eq_basis_sum]
  simp [add_mul, smul_mul_assoc]

@[simp] theorem lower_mul_diagonalLower (v : ThreeSpace) :
    lower v * diagonalLower = 0 := by
  rw [lower_eq_basis_sum]
  simp [add_mul, smul_mul_assoc]

@[simp] theorem diagonalUpper_mul_upper_mul_lower (u v : ThreeSpace) :
    diagonalUpper * (upper u * lower v) = upper u * lower v := by
  have h := Kingdon.Algebra.associator_swap12 formedBilin
    diagonalUpper (upper u) (lower v)
  simp only [diagonalUpper_mul_upper, upper_mul_diagonalUpper,
    diagonalUpper_mul_lower, zero_mul, mul_zero, sub_zero, neg_zero] at h
  exact (sub_eq_zero.mp h).symm

@[simp] theorem diagonalUpper_mul_lower_mul_upper (v u : ThreeSpace) :
    diagonalUpper * (lower v * upper u) = 0 := by
  have h := Kingdon.Algebra.associator_swap12 formedBilin
    diagonalUpper (lower v) (upper u)
  simp only [diagonalUpper_mul_lower, lower_mul_diagonalUpper,
    diagonalUpper_mul_upper, zero_mul, sub_self, neg_zero] at h
  simpa only [zero_sub, neg_eq_zero] using h

@[simp] theorem diagonalLower_mul_upper_mul_lower (u v : ThreeSpace) :
    diagonalLower * (upper u * lower v) = 0 := by
  have h := Kingdon.Algebra.associator_swap12 formedBilin
    diagonalLower (upper u) (lower v)
  simp only [diagonalLower_mul_upper, upper_mul_diagonalLower,
    diagonalLower_mul_lower, zero_mul, sub_self, neg_zero] at h
  simpa only [zero_sub, neg_eq_zero] using h

@[simp] theorem diagonalLower_mul_lower_mul_upper (v u : ThreeSpace) :
    diagonalLower * (lower v * upper u) = lower v * upper u := by
  have h := Kingdon.Algebra.associator_swap12 formedBilin
    diagonalLower (lower v) (upper u)
  simp only [diagonalLower_mul_lower, lower_mul_diagonalLower,
    diagonalLower_mul_upper, zero_mul, mul_zero, sub_zero, neg_zero] at h
  exact (sub_eq_zero.mp h).symm

@[simp] theorem upper_basisVec_mul_lower_basisVec (i : Fin 3) :
    upper (basisVec i) * lower (basisVec i) = diagonalUpper := by
  fin_cases i
  · rfl
  · let p := upper (basisVec 1) * lower (basisVec 1)
    let q := lower (basisVec 1) * upper (basisVec 1)
    have hsum : p + q = 1 := by
      rw [show (1 : AbstractKingdon) =
          basisGenerator 1 * basisGenerator 1 by
        rw [basisGenerator_sq]]
      rw [show basisGenerator 1 =
          upper (basisVec 1) + lower (basisVec 1) by
        exact (upper_add_lower (basisVec 1)).symm]
      simp only [add_mul, mul_add, upper_basisVec_one_sq,
        lower_basisVec_one_sq, zero_add, add_zero, p, q]
      abel
    have hp := congrArg (fun x : AbstractKingdon => diagonalUpper * x) hsum
    simp only [mul_add, diagonalUpper_mul_upper_mul_lower,
      diagonalUpper_mul_lower_mul_upper, add_zero, mul_one, p, q] at hp
    exact hp
  · let p := upper (basisVec 2) * lower (basisVec 2)
    let q := lower (basisVec 2) * upper (basisVec 2)
    have hsum : p + q = 1 := by
      rw [show (1 : AbstractKingdon) =
          basisGenerator 2 * basisGenerator 2 by
        rw [basisGenerator_sq]]
      rw [show basisGenerator 2 =
          upper (basisVec 2) + lower (basisVec 2) by
        exact (upper_add_lower (basisVec 2)).symm]
      simp only [add_mul, mul_add, upper_basisVec_two_sq,
        lower_basisVec_two_sq, zero_add, add_zero, p, q]
      abel
    have hp := congrArg (fun x : AbstractKingdon => diagonalUpper * x) hsum
    simp only [mul_add, diagonalUpper_mul_upper_mul_lower,
      diagonalUpper_mul_lower_mul_upper, add_zero, mul_one, p, q] at hp
    exact hp

@[simp] theorem lower_basisVec_mul_upper_basisVec (i : Fin 3) :
    lower (basisVec i) * upper (basisVec i) = diagonalLower := by
  have hsum :
      upper (basisVec i) * lower (basisVec i) +
        lower (basisVec i) * upper (basisVec i) = 1 := by
    rw [show (1 : AbstractKingdon) =
        basisGenerator i * basisGenerator i by
      rw [basisGenerator_sq]]
    rw [show basisGenerator i =
        upper (basisVec i) + lower (basisVec i) by
      exact (upper_add_lower (basisVec i)).symm]
    fin_cases i <;> simp [add_mul, mul_add] <;> abel
  rw [upper_basisVec_mul_lower_basisVec] at hsum
  exact add_left_cancel (hsum.trans diagonalUpper_add_diagonalLower.symm)

theorem upperLowerRawCyclic {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator i - basisGenerator j * basisGenerator k) *
      (basisGenerator j + basisGenerator k * basisGenerator i) = 0 := by
  simp only [mul_add, sub_mul]
  rw [basisGenerator_mul_rightBivector hik,
    basisBivector_mul_left hjk,
    basisBivector_chain_forward hjk hik.symm hij.symm]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem upperBasis_mul_lowerBasis_cyclic {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i) :
    upper (basisVec i) * lower (basisVec j) = 0 := by
  simp only [upper, lower, hai, haj]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
    ((basisGenerator i - basisGenerator j * basisGenerator k) *
      (basisGenerator j + basisGenerator k * basisGenerator i)) = 0
  rw [upperLowerRawCyclic hij hjk hik]
  simp [scale]

@[simp] theorem upper_basisVec_zero_mul_lower_basisVec_one :
    upper (basisVec 0) * lower (basisVec 1) = 0 := by
  exact upperBasis_mul_lowerBasis_cyclic (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one

@[simp] theorem upper_basisVec_one_mul_lower_basisVec_two :
    upper (basisVec 1) * lower (basisVec 2) = 0 := by
  exact upperBasis_mul_lowerBasis_cyclic (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two

@[simp] theorem upper_basisVec_two_mul_lower_basisVec_zero :
    upper (basisVec 2) * lower (basisVec 0) = 0 := by
  exact upperBasis_mul_lowerBasis_cyclic (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero

theorem upperLowerRawReverse {i j k : Fin 3}
    (hij : i ≠ j) (_hjk : j ≠ k) (_hik : i ≠ k) :
    (basisGenerator j - basisGenerator k * basisGenerator i) *
      (basisGenerator i + basisGenerator j * basisGenerator k) = 0 := by
  simp only [mul_add, sub_mul]
  rw [basisGenerator_mul_leftBivector,
    basisBivector_mul_right,
    basisBivector_chain_reverse (i := j) (j := k) (k := i) hij]
  abel

theorem upperBasis_mul_lowerBasis_reverse {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i) :
    upper (basisVec j) * lower (basisVec i) = 0 := by
  simp only [upper, lower, hai, haj]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
    ((basisGenerator j - basisGenerator k * basisGenerator i) *
      (basisGenerator i + basisGenerator j * basisGenerator k)) = 0
  rw [upperLowerRawReverse hij hjk hik]
  simp [scale]

@[simp] theorem upper_basisVec_one_mul_lower_basisVec_zero :
    upper (basisVec 1) * lower (basisVec 0) = 0 := by
  exact upperBasis_mul_lowerBasis_reverse (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one

@[simp] theorem upper_basisVec_two_mul_lower_basisVec_one :
    upper (basisVec 2) * lower (basisVec 1) = 0 := by
  exact upperBasis_mul_lowerBasis_reverse (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two

@[simp] theorem upper_basisVec_zero_mul_lower_basisVec_two :
    upper (basisVec 0) * lower (basisVec 2) = 0 := by
  exact upperBasis_mul_lowerBasis_reverse (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero

theorem lowerUpperRawProductForward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator i + basisGenerator j * basisGenerator k) *
      (basisGenerator j - basisGenerator k * basisGenerator i) = 0 := by
  simp only [mul_sub, add_mul]
  rw [basisGenerator_mul_rightBivector hik,
    basisBivector_mul_left hjk,
    basisBivector_chain_forward hjk hik.symm hij.symm]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem lowerBasisUpperProductForward {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = basisGenerator j * basisGenerator k)
    (haj : anti (basisVec j) = basisGenerator k * basisGenerator i) :
    lower (basisVec i) * upper (basisVec j) = 0 := by
  simp only [lower, upper, hai, haj]
  rw [scale_mul_scale]
  change scale (2⁻¹ * 2⁻¹)
    ((basisGenerator i + basisGenerator j * basisGenerator k) *
      (basisGenerator j - basisGenerator k * basisGenerator i)) = 0
  rw [lowerUpperRawProductForward hij hjk hik]
  simp [scale]

@[simp] theorem lower_basisVec_zero_mul_upper_basisVec_one :
    lower (basisVec 0) * upper (basisVec 1) = 0 := by
  exact lowerBasisUpperProductForward (by decide) (by decide) (by decide)
    anti_basisVec_zero anti_basisVec_one

@[simp] theorem lower_basisVec_one_mul_upper_basisVec_two :
    lower (basisVec 1) * upper (basisVec 2) = 0 := by
  exact lowerBasisUpperProductForward (by decide) (by decide) (by decide)
    anti_basisVec_one anti_basisVec_two

@[simp] theorem lower_basisVec_two_mul_upper_basisVec_zero :
    lower (basisVec 2) * upper (basisVec 0) = 0 := by
  exact lowerBasisUpperProductForward (by decide) (by decide) (by decide)
    anti_basisVec_two anti_basisVec_zero

theorem lowerUpperRawProductReverse {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (basisGenerator i + -(basisGenerator j * basisGenerator k)) *
      (basisGenerator j - -(basisGenerator k * basisGenerator i)) = 0 := by
  simp only [mul_sub, add_mul, mul_neg_abstract, neg_mul_abstract, neg_neg]
  rw [basisGenerator_mul_rightBivector hik,
    basisBivector_mul_left hjk,
    basisBivector_chain_forward hjk hik.symm hij.symm]
  rw [basisGenerator_anticomm hij.symm]
  abel

theorem lowerBasisUpperProductReverse {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hai : anti (basisVec i) = -(basisGenerator j * basisGenerator k))
    (haj : anti (basisVec j) = -(basisGenerator k * basisGenerator i)) :
    lower (basisVec i) * upper (basisVec j) = 0 := by
  simp only [lower, upper]
  rw [scale_mul_scale]
  rw [hai, haj]
  simp only [basisGenerator]
  have h := congrArg (scale (2⁻¹ * 2⁻¹))
    (lowerUpperRawProductReverse hij hjk hik)
  simpa [basisGenerator, scale] using h

@[simp] theorem lower_basisVec_one_mul_upper_basisVec_zero :
    lower (basisVec 1) * upper (basisVec 0) = 0 := by
  exact lowerBasisUpperProductReverse (i := (1 : Fin 3)) (j := 0) (k := 2)
    (by decide) (by decide) (by decide)
    (by simpa only [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 0)]
      using anti_basisVec_one)
    (by simpa only [basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 2)]
      using anti_basisVec_zero)

@[simp] theorem lower_basisVec_two_mul_upper_basisVec_one :
    lower (basisVec 2) * upper (basisVec 1) = 0 := by
  exact lowerBasisUpperProductReverse (i := (2 : Fin 3)) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
    (by simpa only [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 1)]
      using anti_basisVec_two)
    (by simpa only [basisGenerator_anticomm (by decide : (2 : Fin 3) ≠ 0)]
      using anti_basisVec_one)

@[simp] theorem lower_basisVec_zero_mul_upper_basisVec_two :
    lower (basisVec 0) * upper (basisVec 2) = 0 := by
  exact lowerBasisUpperProductReverse (i := (0 : Fin 3)) (j := 2) (k := 1)
    (by decide) (by decide) (by decide)
    (by simpa only [basisGenerator_anticomm (by decide : (1 : Fin 3) ≠ 2)]
      using anti_basisVec_zero)
    (by simpa only [basisGenerator_anticomm (by decide : (0 : Fin 3) ≠ 1)]
      using anti_basisVec_two)

@[simp] theorem upper_mul_upper (u v : ThreeSpace) :
    upper u * upper v = lower (crossProduct u v) := by
  rw [upper_eq_basis_sum u, upper_eq_basis_sum v, lower_eq_basis_sum]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    upper_basisVec_zero_sq, upper_basisVec_one_sq, upper_basisVec_two_sq,
    upper_basisVec_zero_mul_one, upper_basisVec_zero_mul_two,
    upper_basisVec_one_mul_zero, upper_basisVec_one_mul_two,
    upper_basisVec_two_mul_zero, upper_basisVec_two_mul_one,
    smul_zero_abstract]
  simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
  simp only [smul_smul]
  ring_nf
  simp only [sub_smul_abstract, add_smul_abstract]
  simp only [neg_smul_abstract, smul_smul]
  ring_nf
  abel_nf

@[simp] theorem lower_mul_lower (u v : ThreeSpace) :
    lower u * lower v = -upper (crossProduct u v) := by
  rw [lower_eq_basis_sum u, lower_eq_basis_sum v, upper_eq_basis_sum]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    lower_basisVec_zero_sq, lower_basisVec_one_sq, lower_basisVec_two_sq,
    lower_basisVec_zero_mul_one, lower_basisVec_zero_mul_two,
    lower_basisVec_one_mul_zero, lower_basisVec_one_mul_two,
    lower_basisVec_two_mul_zero, lower_basisVec_two_mul_one,
    smul_zero_abstract]
  simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
  simp only [smul_smul]
  ring_nf
  simp only [sub_smul_abstract, add_smul_abstract]
  simp only [neg_smul_abstract, smul_smul]
  ring_nf
  abel_nf

@[simp] theorem upper_mul_lower (u v : ThreeSpace) :
    upper u * lower v =
      Physics.ZornMatrixSU3.dotProduct u v • diagonalUpper := by
  rw [upper_eq_basis_sum u, lower_eq_basis_sum v]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    upper_basisVec_mul_lower_basisVec,
    upper_basisVec_zero_mul_lower_basisVec_one,
    upper_basisVec_zero_mul_lower_basisVec_two,
    upper_basisVec_one_mul_lower_basisVec_zero,
    upper_basisVec_one_mul_lower_basisVec_two,
    upper_basisVec_two_mul_lower_basisVec_zero,
    upper_basisVec_two_mul_lower_basisVec_one,
    smul_zero_abstract]
  simp [Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  repeat rw [add_smul_abstract] <;>
    simp only [smul_smul] <;> ring_nf <;> abel_nf
  repeat rw [add_smul_abstract]
  abel_nf

@[simp] theorem lower_mul_upper (u v : ThreeSpace) :
    lower u * upper v =
      Physics.ZornMatrixSU3.dotProduct u v • diagonalLower := by
  rw [lower_eq_basis_sum u, upper_eq_basis_sum v]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    lower_basisVec_mul_upper_basisVec,
    lower_basisVec_zero_mul_upper_basisVec_one,
    lower_basisVec_zero_mul_upper_basisVec_two,
    lower_basisVec_one_mul_upper_basisVec_zero,
    lower_basisVec_one_mul_upper_basisVec_two,
    lower_basisVec_two_mul_upper_basisVec_zero,
    lower_basisVec_two_mul_upper_basisVec_one,
    smul_zero_abstract]
  simp [Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  repeat rw [add_smul_abstract] <;>
    simp only [smul_smul] <;> ring_nf <;> abel_nf
  repeat rw [add_smul_abstract]
  abel_nf

/-- Explicit abstract preimage of an arbitrary real Zorn split octonion.

The diagonal is split into its scalar and traceless parts.  This choice makes scalar
matrices read back through the native coefficient embedding, without requiring an
unproved abstract identity between the two diagonal projector expressions. -/
noncomputable def preimage (X : ZornMatrix) : AbstractKingdon :=
  scalar X.b + scale (X.a - X.b) diagonalUpper + upper X.x + lower X.y

theorem preimage_coord (X : ZornMatrix) :
    preimage X =
      X.a • diagonalUpper + X.b • diagonalLower + upper X.x + lower X.y := by
  rw [preimage, scalar_eq_smul_one, scale_eq_smul,
    ← diagonalUpper_add_diagonalLower]
  simp only [smul_add, add_assoc]
  rw [sub_smul_abstract]
  abel

@[simp] theorem preimage_zero : preimage 0 = 0 := by
  simp [preimage, upper, lower, anti, scale, scalar]

@[simp] theorem preimage_add (X Y : ZornMatrix) :
    preimage (X + Y) = preimage X + preimage Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  simp only [preimage, InfoGeometry.Physics.ZornMatrixSU3.add_a,
    InfoGeometry.Physics.ZornMatrixSU3.add_b,
    InfoGeometry.Physics.ZornMatrixSU3.add_x,
    InfoGeometry.Physics.ZornMatrixSU3.add_y, scalar_add, upper_add, lower_add]
  rw [show (a + c) - (b + d) = (a - b) + (c - d) by ring, scale_coeff_add]
  abel

noncomputable def preimageAddHom : ZornMatrix →+ AbstractKingdon where
  toFun := preimage
  map_zero' := preimage_zero
  map_add' := preimage_add

@[simp] theorem preimageAddHom_apply (X : ZornMatrix) : preimageAddHom X = preimage X := rfl

@[simp] theorem realization_preimage (X : ZornMatrix) : realization (preimage X) = X := by
  rcases X with ⟨a, b, x, y⟩
  ext
  · simp [preimage, diagonalUpper, diagonalLower, upper, lower, anti, scale,
      basisVec, generator, InfoGeometry.Physics.ZornMatrixSU3.mul,
      InfoGeometry.Physics.ZornMatrixSU3.add, InfoGeometry.Physics.ZornMatrixSU3.neg,
      InfoGeometry.Physics.ZornMatrixSU3.smul, Physics.ZornMatrixSU3.dotProduct,
      crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · simp [preimage, diagonalUpper, diagonalLower, upper, lower, anti, scale,
      basisVec, generator, InfoGeometry.Physics.ZornMatrixSU3.mul,
      InfoGeometry.Physics.ZornMatrixSU3.add, InfoGeometry.Physics.ZornMatrixSU3.neg,
      InfoGeometry.Physics.ZornMatrixSU3.smul, Physics.ZornMatrixSU3.dotProduct,
      crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [preimage, diagonalUpper, diagonalLower,
      upper, lower, anti, scale, basisVec, generator, InfoGeometry.Physics.ZornMatrixSU3.mul,
      InfoGeometry.Physics.ZornMatrixSU3.add, InfoGeometry.Physics.ZornMatrixSU3.neg,
      InfoGeometry.Physics.ZornMatrixSU3.smul,
      Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · rename_i i; fin_cases i <;> simp [preimage, diagonalUpper, diagonalLower,
      upper, lower, anti, scale, basisVec, generator, InfoGeometry.Physics.ZornMatrixSU3.mul,
      InfoGeometry.Physics.ZornMatrixSU3.add, InfoGeometry.Physics.ZornMatrixSU3.neg,
      InfoGeometry.Physics.ZornMatrixSU3.smul,
      Physics.ZornMatrixSU3.dotProduct, crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

@[simp] theorem preimage_one : preimage 1 = 1 := by
  simp [preimage, upper, lower, anti, scale, scalar]

@[simp] theorem preimage_mul (X Y : ZornMatrix) :
    preimage (X * Y) = preimage X * preimage Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  rw [preimage_coord, preimage_coord, preimage_coord]
  simp [InfoGeometry.Physics.ZornMatrixSU3.mul, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, upper_mul_upper, lower_mul_lower,
    upper_mul_lower, lower_mul_upper]
  have upper_neg_local (w : ThreeSpace) : upper (-w) = -upper w := by
    apply eq_neg_of_add_eq_zero_left
    rw [← upper_add, neg_add_cancel]
    simp [upper, anti, scale, scalar]
  rw [sub_eq_add_neg, upper_add, upper_add, upper_smul, upper_smul,
    upper_neg_local]
  simp only [add_smul_abstract, smul_smul]
  ring_nf
  abel

noncomputable def preimageHom : ZornMatrix →+* AbstractKingdon where
  toFun := preimage
  map_zero' := preimage_zero
  map_one' := preimage_one
  map_add' := preimage_add
  map_mul' := preimage_mul

@[simp] theorem preimageHom_apply (X : ZornMatrix) :
    preimageHom X = preimage X := rfl

theorem realization_comp_preimageAddHom :
    realization.toAddMonoidHom.comp preimageAddHom = AddMonoidHom.id ZornMatrix := by
  apply AddMonoidHom.ext
  intro X
  exact realization_preimage X

theorem realization_comp_preimageHom :
    realization.comp preimageHom = RingHom.id ZornMatrix := by
  apply RingHom.ext
  intro X
  exact realization_preimage X

/-- The realization generates both diagonal and both off-diagonal Zorn coordinates. -/
theorem realization_surjective : Function.Surjective realization := by
  intro X
  exact ⟨preimage X, realization_preimage X⟩

/-- First-isomorphism identification of the reduced Kingdon algebra with the
full real Zorn split-octonion algebra. -/
noncomputable def reducedEquiv :
    (RingCon.ker realization).Quotient ≃+* ZornMatrix :=
  RingCon.quotientKerEquivOfSurjective realization realization_surjective

@[simp] theorem reducedEquiv_mk (x : AbstractKingdon) :
    reducedEquiv (x : (RingCon.ker realization).Quotient) = realization x := by
  exact RingCon.quotientKerEquivOfSurjective_mk realization realization_surjective x

/-- Two abstract Kingdon elements represent the same split octonion exactly
when they are identified by the realization kernel congruence. -/
theorem realization_eq_iff_kernel (x y : AbstractKingdon) :
    realization x = realization y ↔ RingCon.ker realization x y := by
  exact Iff.symm (RingCon.ker_apply realization)

/-- Canonical eight-coordinate representative selected by concrete realization. -/
noncomputable def normalForm (x : AbstractKingdon) : AbstractKingdon :=
  preimage (realization x)

@[simp] theorem normalForm_ι (v : ThreeSpace) :
    normalForm (Kingdon.Algebra.ι formedBilin v) = Kingdon.Algebra.ι formedBilin v := by
  rw [normalForm, realization_ι]
  simp [preimage, generator, scale, scalar, upper_add_lower]

@[simp] theorem normalForm_scalar (r : ℝ) : normalForm (scalar r) = scalar r := by
  rw [normalForm, realization_scalar]
  simp [preimage, upper, lower, anti, scale, scalar,
    InfoGeometry.Physics.ZornMatrixSU3.smul]

theorem preimageHom_comp_realization :
    preimageHom.comp realization = RingHom.id AbstractKingdon := by
  let θ := Kingdon.Algebra.ιLinear formedBilin
  let canonical := Kingdon.Algebra.liftOfLinear formedBilin θ
    (Kingdon.Algebra.alternative_left formedBilin)
    (Kingdon.Algebra.alternative_right formedBilin)
    (by
      intro u v
      change Kingdon.Algebra.ι formedBilin u * Kingdon.Algebra.ι formedBilin v +
        Kingdon.Algebra.ι formedBilin v * Kingdon.Algebra.ι formedBilin u =
        formedBilin u v • (1 : AbstractKingdon)
      rw [← Kingdon.Algebra.scalar_mul formedBilin, mul_one]
      exact Kingdon.Algebra.quadratic formedBilin u v)
    (by
      intro u v w
      exact Kingdon.Algebra.antiassociate formedBilin u v w)
  have hsection : preimageHom.comp realization = canonical := by
    apply Kingdon.Algebra.liftOfLinear_unique formedBilin θ
      (Kingdon.Algebra.alternative_left formedBilin)
      (Kingdon.Algebra.alternative_right formedBilin)
      (by
        intro u v
        change Kingdon.Algebra.ι formedBilin u * Kingdon.Algebra.ι formedBilin v +
          Kingdon.Algebra.ι formedBilin v * Kingdon.Algebra.ι formedBilin u =
          formedBilin u v • (1 : AbstractKingdon)
        rw [← Kingdon.Algebra.scalar_mul formedBilin, mul_one]
        exact Kingdon.Algebra.quadratic formedBilin u v)
      (by
        intro u v w
        exact Kingdon.Algebra.antiassociate formedBilin u v w)
    · intro r
      change normalForm (scalar r) = r • (1 : AbstractKingdon)
      rw [normalForm_scalar, scalar_eq_smul_one]
    · intro v
      change normalForm (Kingdon.Algebra.ι formedBilin v) = θ v
      rw [normalForm_ι]
      rfl
  have hid : RingHom.id AbstractKingdon = canonical := by
    apply Kingdon.Algebra.liftOfLinear_unique formedBilin θ
      (Kingdon.Algebra.alternative_left formedBilin)
      (Kingdon.Algebra.alternative_right formedBilin)
      (by
        intro u v
        change Kingdon.Algebra.ι formedBilin u * Kingdon.Algebra.ι formedBilin v +
          Kingdon.Algebra.ι formedBilin v * Kingdon.Algebra.ι formedBilin u =
          formedBilin u v • (1 : AbstractKingdon)
        rw [← Kingdon.Algebra.scalar_mul formedBilin, mul_one]
        exact Kingdon.Algebra.quadratic formedBilin u v)
      (by
        intro u v w
        exact Kingdon.Algebra.antiassociate formedBilin u v w)
    · intro r
      change scalar r = r • (1 : AbstractKingdon)
      exact scalar_eq_smul_one r
    · intro v
      rfl
  exact hsection.trans hid.symm

@[simp] theorem preimage_realization (x : AbstractKingdon) :
    preimage (realization x) = x := by
  have h := DFunLike.congr_fun preimageHom_comp_realization x
  exact h

@[simp] theorem normalForm_eq (x : AbstractKingdon) : normalForm x = x :=
  preimage_realization x

theorem realization_injective : Function.Injective realization :=
  Function.LeftInverse.injective preimage_realization

theorem realization_ker_eq_bot : RingCon.ker realization = ⊥ := by
  ext x y
  rw [RingCon.ker_apply]
  simp only [realization_injective.eq_iff]
  rfl

@[simp] theorem realization_smul (r : ℝ) (x : AbstractKingdon) :
    realization (r • x) = r • realization x := by
  change realization (scalar r * x) = r • realization x
  rw [map_mul, realization_scalar,
    InfoGeometry.Physics.ZornMatrixSU3.smul_mul_zorn,
    one_mul]

noncomputable def kingdonZornEquiv : AbstractKingdon ≃+* ZornMatrix :=
  RingEquiv.ofBijective realization ⟨realization_injective, realization_surjective⟩

@[simp] theorem kingdonZornEquiv_apply (x : AbstractKingdon) :
    kingdonZornEquiv x = realization x := rfl

@[simp] theorem kingdonZornEquiv_symm_apply (X : ZornMatrix) :
    kingdonZornEquiv.symm X = preimage X := by
  apply realization_injective
  calc
    realization (kingdonZornEquiv.symm X) =
        kingdonZornEquiv (kingdonZornEquiv.symm X) := rfl
    _ = X := kingdonZornEquiv.apply_symm_apply X
    _ = realization (preimage X) := (realization_preimage X).symm

noncomputable def kingdonZornLinearEquiv : AbstractKingdon ≃ₗ[ℝ] ZornMatrix :=
  { kingdonZornEquiv.toEquiv with
    map_add' := realization.map_add
    map_smul' := realization_smul }

@[simp] theorem kingdonZornLinearEquiv_apply (x : AbstractKingdon) :
    kingdonZornLinearEquiv x = realization x := rfl

@[simp] theorem kingdonZornLinearEquiv_symm_apply (X : ZornMatrix) :
    kingdonZornLinearEquiv.symm X = preimage X :=
  kingdonZornEquiv_symm_apply X

noncomputable def zornCoordinateLinearEquiv :
    ZornMatrix ≃ₗ[ℝ] ℝ × ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) where
  toFun := fun X => (X.a, X.b, X.x, X.y)
  invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv X := by cases X; rfl
  right_inv p := by rcases p with ⟨a, b, x, y⟩; rfl
  map_add' X Y := by rfl
  map_smul' r X := by rfl

theorem zornMatrix_finrank : Module.finrank ℝ ZornMatrix = 8 := by
  rw [zornCoordinateLinearEquiv.finrank_eq]
  simp

theorem abstractKingdon_finrank : Module.finrank ℝ AbstractKingdon = 8 := by
  rw [kingdonZornLinearEquiv.finrank_eq]
  exact zornMatrix_finrank

noncomputable def zornFin8LinearEquiv : ZornMatrix ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := fun X => ![X.a, X.b, X.x 0, X.x 1, X.x 2, X.y 0, X.y 1, X.y 2]
  invFun := fun c => ⟨c 0, c 1, ![c 2, c 3, c 4], ![c 5, c 6, c 7]⟩
  left_inv X := by
    rcases X with ⟨a, b, x, y⟩
    apply InfoGeometry.Physics.ZornMatrixSU3.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv c := by
    funext i
    fin_cases i <;> rfl
  map_add' X Y := by
    funext i
    fin_cases i <;> rfl
  map_smul' r X := by
    funext i
    fin_cases i <;> rfl

noncomputable def abstractPeirceCoordinateEquiv :
    AbstractKingdon ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  kingdonZornLinearEquiv.trans zornFin8LinearEquiv

/-- The ordered Peirce-coordinate basis: upper diagonal, lower diagonal,
three upper vectors, then three lower vectors. -/
noncomputable def abstractPeirceBasis : Module.Basis (Fin 8) ℝ AbstractKingdon :=
  Module.Basis.ofEquivFun abstractPeirceCoordinateEquiv

/-- Conjugation on the abstract Kingdon algebra transported from the concrete
real split-octonion model. -/
noncomputable def kingdonConjugate (x : AbstractKingdon) : AbstractKingdon :=
  preimage (conjugate (realization x))

@[simp] theorem realization_kingdonConjugate (x : AbstractKingdon) :
    realization (kingdonConjugate x) = conjugate (realization x) := by
  simp [kingdonConjugate]

@[simp] theorem kingdonConjugate_preimage (X : ZornMatrix) :
    kingdonConjugate (preimage X) = preimage (conjugate X) := by
  simp [kingdonConjugate]

@[simp] theorem kingdonConjugate_involutive (x : AbstractKingdon) :
    kingdonConjugate (kingdonConjugate x) = x := by
  apply realization_injective
  simp [kingdonConjugate, conjugate]

theorem kingdonConjugate_mul (x y : AbstractKingdon) :
    kingdonConjugate (x * y) = kingdonConjugate y * kingdonConjugate x := by
  apply realization_injective
  simp only [realization_kingdonConjugate, map_mul]
  ext i <;> simp [conjugate,
    InfoGeometry.Physics.ZornMatrixSU3.mul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  all_goals (try fin_cases i)
  all_goals try simp
  all_goals ring_nf

@[simp] theorem kingdonConjugate_add (x y : AbstractKingdon) :
    kingdonConjugate (x + y) = kingdonConjugate x + kingdonConjugate y := by
  apply realization_injective
  simp only [realization_kingdonConjugate, map_add]
  ext i <;> simp [conjugate, InfoGeometry.Physics.ZornMatrixSU3.add]
  all_goals ring

@[simp] theorem kingdonConjugate_smul (r : ℝ) (x : AbstractKingdon) :
    kingdonConjugate (r • x) = r • kingdonConjugate x := by
  apply realization_injective
  simp only [realization_kingdonConjugate, realization_smul]
  ext i <;> simp [conjugate, InfoGeometry.Physics.ZornMatrixSU3.smul]

/-- Conjugation as a real-linear involution. Multiplication reversal is exposed
separately by `kingdonConjugate_mul`. -/
noncomputable def kingdonConjugateLinearEquiv :
    AbstractKingdon ≃ₗ[ℝ] AbstractKingdon where
  toFun := kingdonConjugate
  invFun := kingdonConjugate
  left_inv := kingdonConjugate_involutive
  right_inv := kingdonConjugate_involutive
  map_add' := kingdonConjugate_add
  map_smul' := kingdonConjugate_smul

@[simp] theorem kingdonConjugateLinearEquiv_apply (x : AbstractKingdon) :
    kingdonConjugateLinearEquiv x = kingdonConjugate x := rfl

@[simp] theorem kingdonConjugateLinearEquiv_symm :
    kingdonConjugateLinearEquiv.symm = kingdonConjugateLinearEquiv := rfl

@[simp] theorem kingdonConjugate_zero : kingdonConjugate 0 = 0 := by
  apply realization_injective
  simp only [realization_kingdonConjugate, map_zero]
  ext i <;> simp [conjugate]

@[simp] theorem kingdonConjugate_one : kingdonConjugate 1 = 1 := by
  apply realization_injective
  simp only [realization_kingdonConjugate, map_one]
  ext i <;> simp [conjugate]

/-- Conjugation as a ring homomorphism to the opposite algebra. -/
noncomputable def kingdonConjugateOppHom : AbstractKingdon →+* AbstractKingdonᵐᵒᵖ where
  toFun x := MulOpposite.op (kingdonConjugate x)
  map_zero' := by
    exact congrArg MulOpposite.op kingdonConjugate_zero
  map_one' := by
    exact congrArg MulOpposite.op kingdonConjugate_one
  map_add' x y := by
    exact congrArg MulOpposite.op (kingdonConjugate_add x y)
  map_mul' x y := by
    simpa [MulOpposite.op_mul] using congrArg MulOpposite.op (kingdonConjugate_mul x y)

@[simp] theorem kingdonConjugateOppHom_apply (x : AbstractKingdon) :
    kingdonConjugateOppHom x = MulOpposite.op (kingdonConjugate x) := rfl

/-- The split-octonion norm transported to the abstract Kingdon algebra. -/
noncomputable def kingdonNorm (x : AbstractKingdon) : ℝ :=
  norm (realization x)

@[simp] theorem realization_kingdonNorm (x : AbstractKingdon) :
    kingdonNorm x = norm (realization x) := rfl

@[simp] theorem kingdonNorm_mul (x y : AbstractKingdon) :
    kingdonNorm (x * y) = kingdonNorm x * kingdonNorm y := by
  rw [kingdonNorm, map_mul]
  exact InfoGeometry.Physics.ZornMatrixSU3.norm_mul (realization x) (realization y)

@[simp] theorem kingdonNorm_conjugate (x : AbstractKingdon) :
    kingdonNorm (kingdonConjugate x) = kingdonNorm x := by
  simp [kingdonNorm, kingdonConjugate, norm_conjugate]

/-- The split-octonion trace transported to the abstract Kingdon algebra. -/
noncomputable def kingdonTrace (x : AbstractKingdon) : ℝ :=
  (realization x).a + (realization x).b

@[simp] theorem realization_kingdonTrace (x : AbstractKingdon) :
    kingdonTrace x = (realization x).a + (realization x).b := rfl

@[simp] theorem kingdonTrace_add (x y : AbstractKingdon) :
    kingdonTrace (x + y) = kingdonTrace x + kingdonTrace y := by
  simp [kingdonTrace, map_add, InfoGeometry.Physics.ZornMatrixSU3.add]
  ring

@[simp] theorem kingdonTrace_smul (r : ℝ) (x : AbstractKingdon) :
    kingdonTrace (r • x) = r * kingdonTrace x := by
  simp [kingdonTrace, realization_smul, InfoGeometry.Physics.ZornMatrixSU3.smul]
  ring

@[simp] theorem kingdonTrace_conjugate (x : AbstractKingdon) :
    kingdonTrace (kingdonConjugate x) = kingdonTrace x := by
  simp [kingdonTrace, kingdonConjugate, conjugate, add_comm]

/-- The polar form associated to the transported split-octonion norm. -/
noncomputable def kingdonPolar (x y : AbstractKingdon) : ℝ :=
  (kingdonNorm (x + y) - kingdonNorm x - kingdonNorm y) / 2

@[simp] theorem kingdonPolar_symm (x y : AbstractKingdon) :
    kingdonPolar x y = kingdonPolar y x := by
  unfold kingdonPolar
  rw [show x + y = y + x by ac_rfl]
  ring_nf

theorem kingdonPolar_coordinate (x y : AbstractKingdon) :
    kingdonPolar x y =
      ((realization x).a * (realization y).b +
       (realization y).a * (realization x).b -
       InfoGeometry.Physics.ZornMatrixSU3.dotProduct
         (realization x).x (realization y).y -
       InfoGeometry.Physics.ZornMatrixSU3.dotProduct
         (realization y).x (realization x).y) / 2 := by
  simp [kingdonPolar, kingdonNorm, norm, map_add,
    InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem kingdonPolar_add_left (x y z : AbstractKingdon) :
    kingdonPolar (x + y) z = kingdonPolar x z + kingdonPolar y z := by
  rw [kingdonPolar_coordinate, kingdonPolar_coordinate, kingdonPolar_coordinate]
  simp [map_add, InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem kingdonPolar_smul_left (r : ℝ) (x y : AbstractKingdon) :
    kingdonPolar (r • x) y = r * kingdonPolar x y := by
  rw [kingdonPolar_coordinate, kingdonPolar_coordinate]
  simp [realization_smul, InfoGeometry.Physics.ZornMatrixSU3.smul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem kingdonPolar_add_right (x y z : AbstractKingdon) :
    kingdonPolar x (y + z) = kingdonPolar x y + kingdonPolar x z := by
  rw [kingdonPolar_symm x (y + z), kingdonPolar_add_left,
    kingdonPolar_symm y x, kingdonPolar_symm z x]

theorem kingdonPolar_smul_right (r : ℝ) (x y : AbstractKingdon) :
    kingdonPolar x (r • y) = r * kingdonPolar x y := by
  rw [kingdonPolar_symm x (r • y), kingdonPolar_smul_left,
    kingdonPolar_symm y x]

noncomputable def kingdonPolarBilin : LinearMap.BilinForm ℝ AbstractKingdon :=
  LinearMap.mk₂ ℝ kingdonPolar kingdonPolar_add_left kingdonPolar_smul_left
    kingdonPolar_add_right kingdonPolar_smul_right

@[simp] theorem kingdonPolarBilin_apply (x y : AbstractKingdon) :
    kingdonPolarBilin x y = kingdonPolar x y := rfl

/-- The polar form of the split Kingdon norm is nondegenerate. -/
theorem kingdonPolar_nondegenerate (x : AbstractKingdon)
    (h : ∀ y : AbstractKingdon, kingdonPolar x y = 0) : x = 0 := by
  apply realization_injective
  apply InfoGeometry.Physics.ZornMatrixSU3.ext
  · rw [map_zero]
    change (realization x).a = 0
    have ha := h (preimage ⟨0, 1, 0, 0⟩)
    rw [kingdonPolar_coordinate] at ha
    simp [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3] at ha
    linarith
  · rw [map_zero]
    change (realization x).b = 0
    have hb := h (preimage ⟨1, 0, 0, 0⟩)
    rw [kingdonPolar_coordinate] at hb
    simp [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3] at hb
    linarith
  · funext i
    have hx := h (preimage ⟨0, 0, 0, basisVec i⟩)
    rw [kingdonPolar_coordinate] at hx
    fin_cases i <;> simp [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3, basisVec] at hx ⊢ <;> linarith
  · funext i
    have hy := h (preimage ⟨0, 0, basisVec i, 0⟩)
    rw [kingdonPolar_coordinate] at hy
    fin_cases i <;> simp [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3, basisVec] at hy ⊢ <;> linarith

/-- Explicit diagonalization of the transported norm with four positive and
four negative square coordinates. -/
theorem kingdonNorm_signature_four_four (x : AbstractKingdon) :
    kingdonNorm x =
      ((realization x).a + (realization x).b) ^ 2 / 4 +
      ((realization x).x 0 - (realization x).y 0) ^ 2 / 4 +
      ((realization x).x 1 - (realization x).y 1) ^ 2 / 4 +
      ((realization x).x 2 - (realization x).y 2) ^ 2 / 4 -
      ((realization x).a - (realization x).b) ^ 2 / 4 -
      ((realization x).x 0 + (realization x).y 0) ^ 2 / 4 -
      ((realization x).x 1 + (realization x).y 1) ^ 2 / 4 -
      ((realization x).x 2 + (realization x).y 2) ^ 2 / 4 := by
  simp [kingdonNorm, norm, InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem add_conjugate_eq_trace_smul_one (x : AbstractKingdon) :
    x + kingdonConjugate x = kingdonTrace x • (1 : AbstractKingdon) := by
  apply realization_injective
  rw [map_add, realization_kingdonConjugate, realization_smul, map_one]
  ext i <;> simp [kingdonTrace, conjugate,
    InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.smul]
  all_goals ring_nf

theorem mul_conjugate_eq_norm_smul_one (x : AbstractKingdon) :
    x * kingdonConjugate x = kingdonNorm x • (1 : AbstractKingdon) := by
  apply realization_injective
  rw [map_mul, realization_kingdonConjugate, realization_smul, map_one]
  ext i <;> simp [kingdonNorm, norm, conjugate,
    InfoGeometry.Physics.ZornMatrixSU3.mul,
    InfoGeometry.Physics.ZornMatrixSU3.smul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  all_goals (try fin_cases i)
  all_goals try simp
  all_goals ring_nf

theorem conjugate_mul_eq_norm_smul_one (x : AbstractKingdon) :
    kingdonConjugate x * x = kingdonNorm x • (1 : AbstractKingdon) := by
  apply realization_injective
  rw [map_mul, realization_kingdonConjugate, realization_smul, map_one]
  ext i <;> simp [kingdonNorm, norm, conjugate,
    InfoGeometry.Physics.ZornMatrixSU3.mul,
    InfoGeometry.Physics.ZornMatrixSU3.smul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  all_goals (try fin_cases i)
  all_goals try simp
  all_goals ring_nf

/-- Explicit two-sided inverse candidate on the nonzero-norm locus. -/
noncomputable def kingdonInverse (x : AbstractKingdon) : AbstractKingdon :=
  (kingdonNorm x)⁻¹ • kingdonConjugate x

theorem mul_kingdonInverse (x : AbstractKingdon) (h : kingdonNorm x ≠ 0) :
    x * kingdonInverse x = 1 := by
  change x * ((kingdonNorm x)⁻¹ • kingdonConjugate x) = 1
  apply realization_injective
  rw [map_mul, realization_smul, realization_kingdonConjugate, map_one,
    InfoGeometry.Physics.ZornMatrixSU3.mul_smul_zorn]
  have hadj := congrArg realization (mul_conjugate_eq_norm_smul_one x)
  simp only [map_mul, realization_kingdonConjugate, realization_smul, map_one] at hadj
  rw [hadj, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem kingdonInverse_mul (x : AbstractKingdon) (h : kingdonNorm x ≠ 0) :
    kingdonInverse x * x = 1 := by
  change ((kingdonNorm x)⁻¹ • kingdonConjugate x) * x = 1
  apply realization_injective
  rw [map_mul, realization_smul, realization_kingdonConjugate, map_one,
    InfoGeometry.Physics.ZornMatrixSU3.smul_mul_zorn]
  have hadj := congrArg realization (conjugate_mul_eq_norm_smul_one x)
  simp only [map_mul, realization_kingdonConjugate, realization_smul, map_one] at hadj
  rw [hadj, smul_smul, inv_mul_cancel₀ h, one_smul]

@[simp] theorem kingdonNorm_one : kingdonNorm (1 : AbstractKingdon) = 1 := by
  simp [kingdonNorm, InfoGeometry.Physics.ZornMatrixSU3.norm]

/-- The honest nonassociative unit predicate: existence of a two-sided
multiplicative inverse. -/
def IsKingdonUnit (x : AbstractKingdon) : Prop :=
  ∃ y : AbstractKingdon, x * y = 1 ∧ y * x = 1

/-- An abstract Kingdon element has a two-sided inverse exactly when its split
norm is nonzero. No associative `Monoid` instance is assumed. -/
theorem kingdon_isTwoSidedUnit_iff_norm_ne_zero (x : AbstractKingdon) :
    IsKingdonUnit x ↔ kingdonNorm x ≠ 0 := by
  constructor
  · rintro ⟨y, hxy, _⟩ hzero
    have hnorm := congrArg kingdonNorm hxy
    rw [kingdonNorm_mul, hzero, zero_mul, kingdonNorm_one] at hnorm
    norm_num at hnorm
  · intro h
    exact ⟨kingdonInverse x, mul_kingdonInverse x h, kingdonInverse_mul x h⟩

/-- Canonical transport of nonassociative ring automorphisms across the raw
Kingdon--Zorn equivalence. -/
noncomputable def kingdonZornAutomorphismEquiv :
    (AbstractKingdon ≃+* AbstractKingdon) ≃* (ZornMatrix ≃+* ZornMatrix) where
  toFun φ := kingdonZornEquiv.symm.trans (φ.trans kingdonZornEquiv)
  invFun ψ := kingdonZornEquiv.trans (ψ.trans kingdonZornEquiv.symm)
  left_inv φ := by
    apply RingEquiv.ext
    intro x
    change kingdonZornEquiv.symm
      (kingdonZornEquiv (φ (kingdonZornEquiv.symm (kingdonZornEquiv x)))) = φ x
    simp
  right_inv ψ := by
    apply RingEquiv.ext
    intro X
    change kingdonZornEquiv
      (kingdonZornEquiv.symm (ψ (kingdonZornEquiv (kingdonZornEquiv.symm X)))) = ψ X
    simp
  map_mul' φ ψ := by
    apply RingEquiv.ext
    intro X
    change kingdonZornEquiv ((φ * ψ) (kingdonZornEquiv.symm X)) =
      ((kingdonZornEquiv.symm.trans (φ.trans kingdonZornEquiv)) *
        (kingdonZornEquiv.symm.trans (ψ.trans kingdonZornEquiv))) X
    simp

theorem kingdonZornAutomorphismEquiv_intertwine
    (φ : AbstractKingdon ≃+* AbstractKingdon) (x : AbstractKingdon) :
    kingdonZornAutomorphismEquiv φ (kingdonZornEquiv x) =
      kingdonZornEquiv (φ x) := by
  change kingdonZornEquiv (φ (kingdonZornEquiv.symm (kingdonZornEquiv x))) = _
  simp

theorem kingdonZornAutomorphismEquiv_symm_intertwine
    (ψ : ZornMatrix ≃+* ZornMatrix) (X : ZornMatrix) :
    (kingdonZornAutomorphismEquiv.symm ψ) (kingdonZornEquiv.symm X) =
      kingdonZornEquiv.symm (ψ X) := by
  change kingdonZornEquiv.symm
    (ψ (kingdonZornEquiv (kingdonZornEquiv.symm X))) = _
  simp

@[simp] theorem anti_zero : anti 0 = 0 := by
  simp [anti, scale, scalar]

@[simp] theorem upper_zero : upper 0 = 0 := by
  simp [upper, scale, scalar]

@[simp] theorem lower_zero : lower 0 = 0 := by
  simp [lower, scale, scalar]

@[simp] theorem normalForm_upper (v : ThreeSpace) :
    normalForm (upper v) = upper v := by
  exact normalForm_eq (upper v)

@[simp] theorem normalForm_lower (v : ThreeSpace) :
    normalForm (lower v) = lower v := by
  exact normalForm_eq (lower v)

@[simp] theorem realization_normalForm (x : AbstractKingdon) :
    realization (normalForm x) = realization x := by
  rw [normalForm_eq]

@[simp] theorem normalForm_preimage (X : ZornMatrix) :
    normalForm (preimage X) = preimage X := by
  exact normalForm_eq (preimage X)

@[simp] theorem normalForm_idempotent (x : AbstractKingdon) :
    normalForm (normalForm x) = normalForm x := by
  rw [normalForm_eq]

theorem normalForm_add (x y : AbstractKingdon) :
    normalForm (x + y) = normalForm (normalForm x + normalForm y) := by
  simp only [normalForm_eq]

theorem normalForm_mul (x y : AbstractKingdon) :
    normalForm (x * y) = normalForm (normalForm x * normalForm y) := by
  simp only [normalForm_eq]

theorem normalForm_neg (x : AbstractKingdon) :
    normalForm (-x) = normalForm (-normalForm x) := by
  simp only [normalForm_eq]

/-- Compatibility characterization retained for consumers of the former
normal-form/injectivity boundary.  Both sides now hold unconditionally. -/
theorem realization_injective_iff_normalForm :
    Function.Injective realization ↔ ∀ x : AbstractKingdon, normalForm x = x := by
  constructor
  · intro _ x
    exact normalForm_eq x
  · intro _
    exact realization_injective

/-- Equality of canonical representatives is exactly equality modulo the
realization kernel; retained as the quotient-facing compatibility form. -/
theorem normalForm_eq_iff_kernel (x y : AbstractKingdon) :
    normalForm x = normalForm y ↔ RingCon.ker realization x y := by
  rw [← realization_eq_iff_kernel]
  constructor
  · intro h
    simpa only [realization_normalForm] using congrArg realization h
  · intro h
    exact congrArg preimage h

/-- The inverse first-isomorphism map is represented by the explicit
coordinate preimage constructed above. -/
@[simp] theorem reducedEquiv_symm_apply (X : ZornMatrix) :
    reducedEquiv.symm X =
      (preimage X : (RingCon.ker realization).Quotient) := by
  apply reducedEquiv.injective
  simp

end KingdonSplitOctonion
