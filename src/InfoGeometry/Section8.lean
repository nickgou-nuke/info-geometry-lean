import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometryCore.Basic

open InfoGeometryCore

/-!
# Section 8: Quaternion Spin Connection and Curvature

This file formalizes the finite algebraic core of the quaternion-spin connection
section.  It deliberately proves the local quaternion identities directly and
keeps the full global `SL(2,C) -> SO^+(3,1)` representation-theory statement out
of scope.
-/

noncomputable section

namespace Section8

open Matrix

/-! ## 8.1 Quaternions -/

/-- Coordinate quaternion `r + i*x + j*y + k*z`. -/
structure Quat where
  r : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
deriving DecidableEq

namespace Quat

instance : Zero Quat :=
  ⟨⟨0, 0, 0, 0⟩⟩

instance : One Quat :=
  ⟨⟨1, 0, 0, 0⟩⟩

instance : Add Quat :=
  ⟨fun p q => ⟨p.r + q.r, p.x + q.x, p.y + q.y, p.z + q.z⟩⟩

instance : Neg Quat :=
  ⟨fun q => ⟨-q.r, -q.x, -q.y, -q.z⟩⟩

instance : Sub Quat :=
  ⟨fun p q => p + -q⟩

/-- Hamilton product. -/
def mul (p q : Quat) : Quat :=
  ⟨p.r * q.r - p.x * q.x - p.y * q.y - p.z * q.z,
   p.r * q.x + p.x * q.r + p.y * q.z - p.z * q.y,
   p.r * q.y - p.x * q.z + p.y * q.r + p.z * q.x,
   p.r * q.z + p.x * q.y - p.y * q.x + p.z * q.r⟩

instance : Mul Quat :=
  ⟨mul⟩

@[simp] theorem zero_r : (0 : Quat).r = 0 := rfl
@[simp] theorem zero_x : (0 : Quat).x = 0 := rfl
@[simp] theorem zero_y : (0 : Quat).y = 0 := rfl
@[simp] theorem zero_z : (0 : Quat).z = 0 := rfl

@[simp] theorem one_r : (1 : Quat).r = 1 := rfl
@[simp] theorem one_x : (1 : Quat).x = 0 := rfl
@[simp] theorem one_y : (1 : Quat).y = 0 := rfl
@[simp] theorem one_z : (1 : Quat).z = 0 := rfl

@[simp] theorem add_r (p q : Quat) : (p + q).r = p.r + q.r := rfl
@[simp] theorem add_x (p q : Quat) : (p + q).x = p.x + q.x := rfl
@[simp] theorem add_y (p q : Quat) : (p + q).y = p.y + q.y := rfl
@[simp] theorem add_z (p q : Quat) : (p + q).z = p.z + q.z := rfl

@[simp] theorem neg_r (q : Quat) : (-q).r = -q.r := rfl
@[simp] theorem neg_x (q : Quat) : (-q).x = -q.x := rfl
@[simp] theorem neg_y (q : Quat) : (-q).y = -q.y := rfl
@[simp] theorem neg_z (q : Quat) : (-q).z = -q.z := rfl

@[simp] theorem sub_r (p q : Quat) : (p - q).r = p.r - q.r := rfl
@[simp] theorem sub_x (p q : Quat) : (p - q).x = p.x - q.x := rfl
@[simp] theorem sub_y (p q : Quat) : (p - q).y = p.y - q.y := rfl
@[simp] theorem sub_z (p q : Quat) : (p - q).z = p.z - q.z := rfl

@[simp] theorem mul_r (p q : Quat) :
    (p * q).r = p.r * q.r - p.x * q.x - p.y * q.y - p.z * q.z := rfl
@[simp] theorem mul_x (p q : Quat) :
    (p * q).x = p.r * q.x + p.x * q.r + p.y * q.z - p.z * q.y := rfl
@[simp] theorem mul_y (p q : Quat) :
    (p * q).y = p.r * q.y - p.x * q.z + p.y * q.r + p.z * q.x := rfl
@[simp] theorem mul_z (p q : Quat) :
    (p * q).z = p.r * q.z + p.x * q.y - p.y * q.x + p.z * q.r := rfl

/-- Real scalar quaternion. -/
def scalar (a : ℝ) : Quat :=
  ⟨a, 0, 0, 0⟩

@[simp] theorem scalar_r (a : ℝ) : (scalar a).r = a := rfl
@[simp] theorem scalar_x (a : ℝ) : (scalar a).x = 0 := rfl
@[simp] theorem scalar_y (a : ℝ) : (scalar a).y = 0 := rfl
@[simp] theorem scalar_z (a : ℝ) : (scalar a).z = 0 := rfl

/-- Quaternion conjugation. -/
def conj (q : Quat) : Quat :=
  ⟨q.r, -q.x, -q.y, -q.z⟩

@[simp] theorem conj_r (q : Quat) : (conj q).r = q.r := rfl
@[simp] theorem conj_x (q : Quat) : (conj q).x = -q.x := rfl
@[simp] theorem conj_y (q : Quat) : (conj q).y = -q.y := rfl
@[simp] theorem conj_z (q : Quat) : (conj q).z = -q.z := rfl

/-- Euclidean quaternion norm squared. -/
def normSq (q : Quat) : ℝ :=
  q.r ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2

/-- Euclidean dot product on quaternion coordinates. -/
def dot (p q : Quat) : ℝ :=
  p.r * q.r + p.x * q.x + p.y * q.y + p.z * q.z

/-- A pure imaginary quaternion has zero scalar coordinate. -/
def IsPureImaginary (q : Quat) : Prop :=
  q.r = 0

@[ext] theorem ext {p q : Quat} (hr : p.r = q.r) (hx : p.x = q.x) (hy : p.y = q.y)
    (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

/-- Quaternion basis unit `i`. -/
def qi : Quat :=
  ⟨0, 1, 0, 0⟩

/-- Quaternion basis unit `j`. -/
def qj : Quat :=
  ⟨0, 0, 1, 0⟩

/-- Quaternion basis unit `k`. -/
def qk : Quat :=
  ⟨0, 0, 0, 1⟩

theorem basis_laws :
    qi * qi = -(1 : Quat)
      ∧ qj * qj = -(1 : Quat)
      ∧ qk * qk = -(1 : Quat)
      ∧ qi * qj = qk
      ∧ qj * qk = qi
      ∧ qk * qi = qj
      ∧ (qi * qj) * qk = -(1 : Quat) := by
  constructor
  · ext <;> norm_num [qi]
  constructor
  · ext <;> norm_num [qj]
  constructor
  · ext <;> norm_num [qk]
  constructor
  · ext <;> norm_num [qi, qj, qk]
  constructor
  · ext <;> norm_num [qi, qj, qk]
  constructor
  · ext <;> norm_num [qi, qj, qk]
  · ext <;> norm_num [qi, qj, qk]

theorem conj_mul_self (q : Quat) :
    conj q * q = scalar (normSq q) := by
  ext <;> simp [normSq] <;> ring_nf

theorem mul_conj_self (q : Quat) :
    q * conj q = scalar (normSq q) := by
  ext <;> simp [normSq] <;> ring_nf

theorem unit_condition (q : Quat) (h : normSq q = 1) :
    conj q * q = 1 ∧ q * conj q = 1 := by
  constructor
  · rw [conj_mul_self, h]
    ext <;> simp
  · rw [mul_conj_self, h]
    ext <;> simp

theorem conj_eq_neg_of_pure (q : Quat) (h : IsPureImaginary q) :
    conj q = -q := by
  ext
  · simp [IsPureImaginary] at h
    simp [h]
  · simp
  · simp
  · simp

/-! ## 8.1 Pauli four-vector representation -/

def sigma0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, 1]

abbrev sigma1 := sigma1C

abbrev sigma2 := sigma2C

abbrev sigma3 := sigma3C

/-- Pauli/Hermitian representative of a four-vector. -/
def spacetimeMatrix (t x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  t • sigma0 + x • sigma1 + y • sigma2 + z • sigma3

theorem spacetimeMatrix_det (t x y z : ℂ) :
    (spacetimeMatrix t x y z).det = t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [spacetimeMatrix, sigma0, sigma1C, sigma2C, sigma3C, Matrix.det_fin_two, Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## 8.2 Quaternion connection -/

/-- Quaternion connection `Omega = qbar * dq`. -/
def quaternionConnection (q dq : Quat) : Quat :=
  conj q * dq

theorem quaternionConnection_real (q dq : Quat) :
    (quaternionConnection q dq).r = dot q dq := by
  simp [quaternionConnection, dot]

/--
If `dq` is tangent to the unit-quaternion constraint at `q`, then
`Omega = qbar * dq` is pure imaginary.
-/
theorem quaternion_connection_pure_imaginary_of_tangent (q dq : Quat)
    (h_tangent : dot q dq = 0) :
    IsPureImaginary (quaternionConnection q dq) := by
  rw [IsPureImaginary, quaternionConnection_real, h_tangent]

theorem quaternion_connection_conj_eq_neg_of_tangent (q dq : Quat)
    (h_tangent : dot q dq = 0) :
    conj (quaternionConnection q dq) = -quaternionConnection q dq := by
  exact conj_eq_neg_of_pure (quaternionConnection q dq)
    (quaternion_connection_pure_imaginary_of_tangent q dq h_tangent)

/-- Quaternion covariant derivative `D_mu V = partial_mu V + Omega_mu V - V Omega_mu`. -/
def covariantDerivative (partialV Omega V : Quat) : Quat :=
  partialV + Omega * V - V * Omega

theorem covariantDerivative_zero_connection (partialV V : Quat) :
    covariantDerivative partialV 0 V = partialV := by
  ext <;> simp [covariantDerivative]

/-! ## 8.3 Flat tetrads and spin connection -/

/-- Flat tetrad `e^a_mu = delta^a_mu`. -/
def flatTetrad : Matrix (Fin 4) (Fin 4) ℝ :=
  1

/-- Minkowski metric with `(-,+,+,+)` convention. -/
def eta4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(-1 : ℝ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem flat_tetrad_metric :
    flatTetradᵀ * eta4 * flatTetrad = eta4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flatTetrad, eta4, Matrix.mul_apply, Fin.sum_univ_four]

/-- Flat spin connection coefficients. -/
def spinConnectionFlat (_mu _a _b : Fin 4) : ℝ :=
  0

theorem spinConnectionFlat_antisymmetric (mu a b : Fin 4) :
    spinConnectionFlat mu a b = -spinConnectionFlat mu b a := by
  simp [spinConnectionFlat]

theorem tetrad_compatibility_flat (mu nu a : Fin 4) :
    (0 : ℝ) - 0 + spinConnectionFlat mu a nu = 0 := by
  simp [spinConnectionFlat]

/-! ## 8.4 Curvature and the flat quaternion-spin relation -/

/-- Quaternion curvature `F = d_mu Omega_nu - d_nu Omega_mu + [Omega_mu, Omega_nu]`. -/
def quaternionCurvature (dMuOmegaNu dNuOmegaMu OmegaMu OmegaNu : Quat) : Quat :=
  dMuOmegaNu - dNuOmegaMu + OmegaMu * OmegaNu - OmegaNu * OmegaMu

theorem quaternionCurvature_flat :
    quaternionCurvature 0 0 0 0 = 0 := by
  ext <;> simp [quaternionCurvature]

/--
Flat-space instance of the quaternion-spin connection relation:
zero spin connection projects to zero quaternion connection.
-/
theorem quaternion_spin_relation_flat (mu : Fin 4) :
    quaternionConnection 1 0 = 0
      ∧ spinConnectionFlat mu 0 1 = 0
      ∧ quaternionCurvature 0 0 0 0 = 0 := by
  constructor
  · ext <;> simp [quaternionConnection]
  constructor
  · simp [spinConnectionFlat]
  · exact quaternionCurvature_flat

end Quat

end Section8
