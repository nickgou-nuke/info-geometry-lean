/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative operator identities suggested by the HR archetypes

This file formalizes finite matrix and star-ring identities over possibly
noncommutative rings. A Hermitian square is not called positive without an
ordered positive-cone structure. These declarations do not construct Weil
cohomology, zeta functions, a geometric Fourier transform, or an analytic
Riemann-hypothesis argument.
-/

namespace InfoGeometry.Algebra.NoncommutativeWeilPicardLefschetz

open Matrix

universe u

def mat2 {A : Type u} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

theorem mat2_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨mat2 0 1 0 0, mat2 0 0 1 0, ?_⟩
  intro h
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
  simp [mat2, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem mat2_noncomm_witness_B {B : Type u} [Ring B] [Nontrivial B] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) B, X * Y ≠ Y * X :=
  mat2_noncomm_witness

theorem mat2_ext {A : Type u} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section HR1_Discriminant

variable {B : Type u} [Ring B] [StarRing B]

/-- Universal noncommutative discriminant identity; the commutator is explicit. -/
theorem star_discriminant_identity (F : B) :
    4 • (star F * F) - star (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆ := by
  rw [Ring.lie_def]
  simp only [star_add, star_sub, star_star, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

/-- Under normality, the discriminant is exactly a Hermitian square.
No order or positivity structure on `B` is assumed. -/
theorem normal_discriminant_is_hermitian_square (F : B)
    (hnormal : ⁅star F, F⁆ = 0) :
    4 • (star F * F) - (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) := by
  have hself : star (F + star F) = F + star F := by
    simp [star_add, add_comm]
  calc
    4 • (star F * F) - (F + star F) * (F + star F) =
        4 • (star F * F) - star (F + star F) * (F + star F) := by rw [hself]
    _ = star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆ :=
        star_discriminant_identity F
    _ = star (F - star F) * (F - star F) := by rw [hnormal]; simp

/-- Noncommutative quadratic-pencil polarization identity. -/
theorem quadratic_pencil_polarization (F : B) (m n : ℕ) :
    star ((2 * m) • (1 : B) - n • (F + star F)) *
        ((2 * m) • (1 : B) - n • (F + star F)) +
      star (n • (F - star F)) * (n • (F - star F)) =
    2 • (star (m • (1 : B) - n • F) * (m • (1 : B) - n • F)) +
      2 • ((m • (1 : B) - n • F) * star (m • (1 : B) - n • F)) := by
  simp only [star_add, star_sub, star_nsmul, star_one, star_star]
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  noncomm_ring

end HR1_Discriminant

section HR2_QuaternionAndTrace

variable {A : Type u} [Ring A]

theorem trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

variable [StarRing A]

def rotor (a b : A) : Matrix (Fin 2) (Fin 2) A := mat2 a (-b) b a
def quaternionI : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def quaternionJ (ι : A) : Matrix (Fin 2) (Fin 2) A := mat2 ι 0 0 (-ι)
def quaternionK (ι : A) : Matrix (Fin 2) (Fin 2) A := mat2 0 ι ι 0

/-- The matrix Hilbert--Schmidt trace is an exact algebraic sum, not a positivity claim. -/
theorem rotor_star_trace (a b : A) :
    Matrix.trace ((rotor a b)ᴴ * rotor a b) =
      2 • (star a * a + star b * b) := by
  rw [trace_fin2]
  simp [rotor, mat2, Matrix.mul_apply, Fin.sum_univ_two,
    two_smul, add_comm, add_left_comm, add_assoc]

/-- Quaternion relations in `M₂(A)` from an internal square root of `-1`.
This proves the relations, not faithfulness or a quaternion-algebra equivalence. -/
theorem quaternion_matrix_relations {ι : A} (hι : ι * ι = -1) :
    quaternionI (A := A) * quaternionI = -1 ∧
    quaternionJ ι * quaternionJ ι = -1 ∧
    quaternionK ι * quaternionK ι = -1 ∧
    quaternionI * quaternionJ ι = quaternionK ι ∧
    quaternionJ ι * quaternionI = -quaternionK ι ∧
    ⁅quaternionI (A := A), quaternionJ ι⁆ = 2 • quaternionK ι := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [quaternionI, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [quaternionJ, mat2, Matrix.mul_apply, Fin.sum_univ_two, hι]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [quaternionK, mat2, Matrix.mul_apply, Fin.sum_univ_two, hι]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [quaternionI, quaternionJ, quaternionK, mat2,
        Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [quaternionI, quaternionJ, quaternionK, mat2,
        Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Ring.lie_def]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [quaternionI, quaternionJ, quaternionK, mat2,
        Matrix.mul_apply, Fin.sum_univ_two, two_smul]

theorem rotor_similitudes (a b : A) (hsa : star a = a) (hsb : star b = b)
    (hcomm : a * b = b * a) :
    (rotor a b)ᴴ * (mat2 0 (-1) 1 0) * rotor a b =
        mat2 0 (-(a * a + b * b)) (a * a + b * b) 0 ∧
    (rotor a b)ᴴ * rotor a b = mat2 (a * a + b * b) 0 0 (a * a + b * b) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotor, mat2, Matrix.mul_apply, Fin.sum_univ_two,
      hsa, hsb, hcomm] <;> abel

end HR2_QuaternionAndTrace

section HR3_KahlerCayley

variable {A : Type u} [Ring A] [StarRing A]

def omega : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def sigma : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def gamma : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def scalarMatrix (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

def symplecticPairing (X Y : Matrix (Fin 2) (Fin 2) A) := Xᴴ * omega * Y
def compatibleMetric (X Y : Matrix (Fin 2) (Fin 2) A) :=
  -symplecticPairing X (omega * Y)
def cayley : Matrix (Fin 2) (Fin 2) A := 1 + omega

theorem omega_sq : omega (A := A) * omega = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omega, mat2, Matrix.mul_apply, Fin.sum_univ_two]

theorem compatibleMetric_eq_inner (X Y : Matrix (Fin 2) (Fin 2) A) :
    compatibleMetric X Y = Xᴴ * Y := by
  dsimp [compatibleMetric, symplecticPairing]
  calc
    -(Xᴴ * omega * (omega * Y)) = -(Xᴴ * (omega * omega) * Y) := by noncomm_ring
    _ = -(Xᴴ * (-1) * Y) := by rw [omega_sq (A := A)]
    _ = Xᴴ * Y := by noncomm_ring

theorem cayley_plancherel :
    cayleyᴴ * cayley = 2 • (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cayley, omega, mat2, Matrix.mul_apply, Fin.sum_univ_two,
      two_smul] <;> abel

theorem cayley_rotates_grading :
    (cayley (A := A) : Matrix (Fin 2) (Fin 2) A) * gamma *
      (cayley (A := A) : Matrix (Fin 2) (Fin 2) A)ᴴ =
        2 • (sigma (A := A)) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cayley, gamma, sigma, omega, mat2, Matrix.mul_apply,
      Fin.sum_univ_two, two_smul] <;> abel

end HR3_KahlerCayley

section HR4_EvenPowersCutoffsAndTransvections

variable {B : Type u} [Ring B] [StarRing B]

/-- Even powers of a self-adjoint element are Hermitian squares. -/
theorem selfAdjoint_even_power_square (t : B) (ht : star t = t) (m : ℕ) :
    t ^ (2 * m) = star (t ^ m) * (t ^ m) := by
  rw [star_pow, ht, two_mul, pow_add]

/-- Exact compression/complement energy decomposition for a self-adjoint
idempotent and a scalar-like element commuting with it. -/
theorem projection_cutoff_energy (U P q : B)
    (hU : star U * U = q) (hP : P * P = P) (hPstar : star P = P)
    (hcomm : P * q = q * P) :
    star (P * U * P) * (P * U * P) +
      star ((1 - P) * U * P) * ((1 - P) * U * P) = q * P := by
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  simp only [star_mul, star_sub, star_one, hPstar]
  calc
    _ = P * star U * P * P * U * P +
        P * star U * (1 - P) * (1 - P) * U * P := by noncomm_ring
    _ = P * star U * (P * P) * U * P +
        P * star U * ((1 - P) * (1 - P)) * U * P := by noncomm_ring
    _ = P * star U * P * U * P + P * star U * (1 - P) * U * P := by
      rw [hP, hcomp]
    _ = P * star U * (P + (1 - P)) * U * P := by noncomm_ring
    _ = P * star U * U * P := by noncomm_ring
    _ = P * (star U * U) * P := by noncomm_ring
    _ = P * q * P := by rw [hU]
    _ = q * (P * P) := by
      rw [hcomm]
      noncomm_ring
    _ = q * P := by rw [hP]

def transvectionGenerator (P : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 (-P) (-P) P P
def transvection (P : B) : Matrix (Fin 2) (Fin 2) B :=
  1 + transvectionGenerator P
def symplecticForm : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0

theorem transvectionGenerator_sq_zero (P : B) :
    transvectionGenerator P * transvectionGenerator P = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [transvectionGenerator, mat2, Matrix.mul_apply, Fin.sum_univ_two]

theorem transvectionGenerator_hamiltonian (P : B) (hP : star P = P) :
    star (transvectionGenerator P) * symplecticForm +
      symplecticForm * transvectionGenerator P = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [transvectionGenerator, symplecticForm, mat2,
      Matrix.mul_apply, Fin.sum_univ_two, hP]

theorem transvectionGenerator_isotropic (P : B) (hP : star P = P) :
    star (transvectionGenerator P) * symplecticForm *
      transvectionGenerator P = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [transvectionGenerator, symplecticForm, mat2,
      Matrix.mul_apply, Fin.sum_univ_two, hP]

theorem transvection_pow (P : B) (k : ℕ) :
    transvection P ^ k = 1 + k • transvectionGenerator P := by
  induction k with
  | zero => simp [transvection]
  | succ k ih =>
      rw [pow_succ, ih, transvection, add_nsmul, one_nsmul]
      have hmul : (k • transvectionGenerator P) * transvectionGenerator P = 0 := by
        rw [nsmul_eq_mul, mul_assoc, transvectionGenerator_sq_zero, mul_zero]
      calc
        (1 + k • transvectionGenerator P) *
            (1 + transvectionGenerator P) =
          1 + (k • transvectionGenerator P + transvectionGenerator P) +
            (k • transvectionGenerator P) * transvectionGenerator P := by
              noncomm_ring
        _ = 1 + (k • transvectionGenerator P + transvectionGenerator P) := by
              rw [hmul, add_zero]

theorem transvection_preserves_symplectic_form (P : B) (hP : star P = P)
    (k : ℕ) :
    star (transvection P ^ k) * symplecticForm *
      (transvection P ^ k) = symplecticForm := by
  have hham := transvectionGenerator_hamiltonian P hP
  have hiso := transvectionGenerator_isotropic P hP
  have hstep : star (transvection P) * symplecticForm * transvection P =
      symplecticForm := by
    dsimp [transvection]
    simp only [star_add, star_one]
    calc
      (1 + star (transvectionGenerator P)) * symplecticForm *
          (1 + transvectionGenerator P) =
        symplecticForm +
          (star (transvectionGenerator P) * symplecticForm +
            symplecticForm * transvectionGenerator P) +
          star (transvectionGenerator P) * symplecticForm *
            transvectionGenerator P := by noncomm_ring
      _ = symplecticForm := by rw [hham, hiso]; abel
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, star_mul]
      calc
        star (transvection P) * star (transvection P ^ k) * symplecticForm *
            (transvection P ^ k * transvection P) =
          star (transvection P) *
            (star (transvection P ^ k) * symplecticForm * transvection P ^ k) *
            transvection P := by noncomm_ring
        _ = star (transvection P) * symplecticForm * transvection P := by rw [ih]
        _ = symplecticForm := hstep

end HR4_EvenPowersCutoffsAndTransvections

end InfoGeometry.Algebra.NoncommutativeWeilPicardLefschetz
