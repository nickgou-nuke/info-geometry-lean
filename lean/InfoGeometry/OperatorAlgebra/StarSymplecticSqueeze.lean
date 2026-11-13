/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.OperatorValuedJones
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Group.Commute.Basic

/-!
# Star-form Lie algebras and faithful squeeze representations

Over an arbitrary star ring, the infinitesimal equation `star x * j + j * x = 0`
defines a native integer Lie subalgebra. The form-preserving group is constructed
inside the units, so a one-sided isometry equation is never used to assume an
inverse. On two-by-two operator matrices the existing Jones generators give the
standard skew form. Starred inverse blocks define a faithful group homomorphism.

The unstarred clock/shift dilation has a different multiplication law; it is
multiplicative precisely on commuting pairs of units. No analytic exponential,
Mellin transform, or identification with the spacetime DeWitt form is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.StarSymplecticSqueeze

open Matrix InfoGeometry.Clifford

section StarForms

variable {A : Type*} [Ring A] [StarRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The infinitesimal isometries of a fixed star-form element, over integers. -/
def formLie (j : A) : LieSubalgebra ℤ A where
  carrier := {x | star x * j + j * x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change star (x + y) * j + j * (x + y) = 0
    rw [star_add, add_mul, mul_add]
    calc
      (star x * j + star y * j) + (j * x + j * y) =
          (star x * j + j * x) + (star y * j + j * y) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  smul_mem' := by
    intro n x hx
    change star (n • x) * j + j * (n • x) = 0
    rw [star_zsmul, smul_mul_assoc, mul_smul_comm, ← smul_add, hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    change star (x * y - y * x) * j + j * (x * y - y * x) = 0
    have hx' : star x * j = -(j * x) := eq_neg_of_add_eq_zero_left hx
    have hy' : star y * j = -(j * y) := eq_neg_of_add_eq_zero_left hy
    rw [star_sub, star_mul, star_mul]
    calc
      (star y * star x - star x * star y) * j + j * (x * y - y * x) =
          star y * (star x * j) - star x * (star y * j) +
            j * (x * y - y * x) := by noncomm_ring
      _ = -(star y * (j * x)) + star x * (j * y) +
          j * (x * y - y * x) := by rw [hx', hy']; noncomm_ring
      _ = -((star y * j) * x) + (star x * j) * y +
          j * (x * y - y * x) := by noncomm_ring
      _ = 0 := by simp only [hx', hy']; noncomm_ring

@[simp] theorem mem_formLie (j x : A) :
    x ∈ formLie j ↔ star x * j + j * x = 0 := Iff.rfl

/-- Actual units preserving the fixed star form. No inverse is inferred from
the form equation alone. -/
def formGroup (j : A) : Subgroup Aˣ where
  carrier := {u | star (u : A) * j * (u : A) = j}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change star ((u : A) * (v : A)) * j * ((u : A) * (v : A)) = j
    rw [star_mul]
    calc
      star (v : A) * star (u : A) * j * ((u : A) * (v : A)) =
          star (v : A) * (star (u : A) * j * (u : A)) * (v : A) := by
            noncomm_ring
      _ = j := by rw [hu, hv]
  inv_mem' := by
    intro u hu
    change star (↑u⁻¹ : A) * j * (↑u⁻¹ : A) = j
    calc
      star (↑u⁻¹ : A) * j * (↑u⁻¹ : A) =
          star (↑u⁻¹ : A) * (star (u : A) * j * (u : A)) * (↑u⁻¹ : A) := by
            rw [hu]
      _ = (star (↑u⁻¹ : A) * star (u : A)) * j * ((u : A) * (↑u⁻¹ : A)) := by
        noncomm_ring
      _ = j := by rw [← star_mul]; simp

@[simp] theorem mem_formGroup (j : A) (u : Aˣ) :
    u ∈ formGroup j ↔ star (u : A) * j * (u : A) = j := Iff.rfl

end StarForms

section ClockShift

variable {B : Type*} [Ring B]

/-- The operator-valued clock, with its lower eigenvalue replaced by a ring element. -/
def clock (a : B) : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, a]

/-- The unstarred dilation used by the clock/shift relation. -/
def dilation (u : Bˣ) : Matrix (Fin 2) (Fin 2) B :=
  !![(u : B), 0; 0, (↑u⁻¹ : B)]

theorem clock_shift_braiding (u : Bˣ) :
    J_mat * clock (u : B) = dilation u * clock (u : B) * J_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, clock, dilation, Matrix.mul_apply, Fin.sum_univ_two]

theorem dilation_shift_inversion (u : Bˣ) :
    J_mat * dilation u * J_mat = dilation u⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, dilation, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exact obstruction to treating the unstarred dilation as a group map. -/
theorem dilation_mul_iff (u v : Bˣ) :
    dilation (u * v) = dilation u * dilation v ↔ Commute u v := by
  constructor
  · intro h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 1 1) h
    have hi : v⁻¹ * u⁻¹ = u⁻¹ * v⁻¹ := by
      apply Units.ext
      simpa [dilation, Matrix.mul_apply, Fin.sum_univ_two] using h11
    exact Commute.inv_inv_iff.mp hi.symm
  · intro h
    have hi : (↑v⁻¹ : B) * (↑u⁻¹ : B) = (↑u⁻¹ : B) * (↑v⁻¹ : B) :=
      congrArg (fun z : Bˣ => (z : B)) h.inv_inv.eq.symm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilation, Matrix.mul_apply, Fin.sum_univ_two, hi]

end ClockShift

section MatrixStarForm

variable {B : Type*} [Ring B] [StarRing B]

/-- The intake's skew generator, with its sign related to the existing Jones basis. -/
def omega : Matrix (Fin 2) (Fin 2) B := -K_mat

omit [StarRing B] in
@[simp] theorem omega_eq : omega (B := B) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omega, K_mat]

/-- Exact Hamiltonian block classification over an arbitrary noncommutative star ring. -/
theorem mem_formLie_omega_iff (X : Matrix (Fin 2) (Fin 2) B) :
    X ∈ formLie (omega (B := B)) ↔
      X 1 1 = -star (X 0 0) ∧ star (X 0 1) = X 0 1 ∧ star (X 1 0) = X 1 0 := by
  rw [mem_formLie]
  change Xᴴ * omega + omega * X = 0 ↔ _
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 1) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 1 1) h
    simp only [omega_eq, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.zero_apply] at h00 h01 h11
    simp at h00 h01 h11
    have hd : X 1 1 + star (X 0 0) = 0 := by
      simpa only [neg_add, neg_neg, neg_zero, add_comm] using congrArg Neg.neg h01
    exact ⟨eq_neg_of_add_eq_zero_left hd,
      neg_add_eq_zero.mp h11, (eq_neg_of_add_eq_zero_left h00).trans (neg_neg _)⟩
  · rintro ⟨hd, hb, hc⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, hd, hb, hc]

def hamiltonianBlock (a b c : B) : Matrix (Fin 2) (Fin 2) B :=
  !![a, b; c, -star a]

theorem hamiltonianBlock_mem (a b c : B) (hb : star b = b) (hc : star c = c) :
    hamiltonianBlock a b c ∈ formLie (omega (B := B)) := by
  rw [mem_formLie_omega_iff]
  exact ⟨rfl, hb, hc⟩

theorem grading_mem_formLie : Gamma_mat (B := B) ∈ formLie omega := by
  rw [mem_formLie_omega_iff]
  simp [Gamma_mat]

/-- The starred inverse block retains the order of arbitrary operator products. -/
def squeeze (u : Bˣ) : Matrix (Fin 2) (Fin 2) B :=
  !![(u : B), 0; 0, star (↑u⁻¹ : B)]

@[simp] theorem squeeze_one : squeeze (1 : Bˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [squeeze]

theorem squeeze_mul (u v : Bˣ) : squeeze (u * v) = squeeze u * squeeze v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squeeze, Matrix.mul_apply, Fin.sum_univ_two]

/-- The inverse is constructed, not inferred from preservation of the form. -/
def squeezeUnit (u : Bˣ) : (Matrix (Fin 2) (Fin 2) B)ˣ where
  val := squeeze u
  inv := squeeze u⁻¹
  val_inv := by rw [← squeeze_mul, mul_inv_cancel, squeeze_one]
  inv_val := by rw [← squeeze_mul, inv_mul_cancel, squeeze_one]

theorem squeeze_preserves (u : Bˣ) :
    (squeeze u)ᴴ * omega * squeeze u = omega := by
  have hstar : star (u : B) * star (↑u⁻¹ : B) = 1 := by
    rw [← star_mul, Units.inv_mul, star_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squeeze, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, hstar]

/-- A faithful native group representation into units preserving the skew form. -/
def squeezeHom : Bˣ →* formGroup (omega (B := B)) where
  toFun u := ⟨squeezeUnit u, squeeze_preserves u⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact squeeze_one
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    exact squeeze_mul u v

theorem squeezeHom_injective : Function.Injective (squeezeHom (B := B)) := by
  intro u v h
  apply Units.ext
  exact congrArg (fun z : formGroup (omega (B := B)) => z.val.val 0 0) h

end MatrixStarForm

end InfoGeometry.OperatorAlgebra.StarSymplecticSqueeze
