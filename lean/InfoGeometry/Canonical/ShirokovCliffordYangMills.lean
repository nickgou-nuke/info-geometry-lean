/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KahlerAtiyahSpinConnection
import InfoGeometry.Canonical.ShirokovYangMillsTransfer
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
import InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Clifford-vector specialization of Shirokov's Yang--Mills transfer

This is a conditional finite-coordinate form of Theorem 5.2. It combines the
Kähler--Atiyah Clifford action and its contracted cubic commutator with the
abstract `C + K` Yang--Mills transfer. Flatness and parallelness of the
background are hypotheses here; deriving them from a varying Clifford frame
is a separate open bridge.
-/

noncomputable section
set_option maxHeartbeats 500000

namespace InfoGeometry.Canonical.ShirokovCliffordYangMills

open InfoGeometry.Canonical.KahlerAtiyahCartanForms
open InfoGeometry.Canonical.KahlerAtiyahSpinConnection
open InfoGeometry.Canonical.ShirokovYangMillsTransfer
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions

/-- The integer eigenvalue appearing in Shirokov's grade-projection
coefficient matrix. The paper's one-based index `i` is represented by
`i - 1` here. -/
def shirokovGradeEigenvalue (n i : ℕ) : ℤ :=
  (-1 : ℤ) ^ i * ((n : ℤ) - 2 * (i : ℤ))

/-- In even dimension, every denominator `n - λ_i` used by the full
grade-projection formula (for `1 ≤ i ≤ n`) is strictly positive. This
establishes that the displayed scalar coefficients are defined; it does not
establish invertibility of the separate Vandermonde coefficient matrix. -/
theorem shirokov_even_grade_projection_denominator_pos
    {n i : ℕ} (hn : Even n) (hi : 0 < i) (hin : i ≤ n) :
    0 < (n : ℤ) - shirokovGradeEigenvalue n i := by
  have hiBound : 0 < i := hi
  have hinBound : i ≤ n := hin
  by_cases hiEven : Even i
  · obtain ⟨k, rfl⟩ := hiEven
    have hp : (-1 : ℤ) ^ (k + k) = 1 := by
      rw [← two_mul k, pow_mul]
      norm_num
    unfold shirokovGradeEigenvalue
    rw [hp]
    push_cast
    have hkpos : 0 < k := by omega
    omega
  · obtain ⟨k, rfl⟩ := (Nat.not_even_iff_odd.mp hiEven)
    obtain ⟨l, rfl⟩ := hn
    have hpEven : (-1 : ℤ) ^ (k + k) = 1 := by
      rw [← two_mul k, pow_mul]
      norm_num
    have hp : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
      calc
        (-1 : ℤ) ^ (2 * k + 1) = (-1 : ℤ) ^ (2 * k) * (-1) := by
          rw [pow_succ]
        _ = (-1 : ℤ) ^ (k + k) * (-1) := by rw [show 2 * k = k + k by omega]
        _ = -1 := by rw [hpEven]; norm_num
    unfold shirokovGradeEigenvalue
    rw [hp]
    push_cast
    have hklt : k < l := by omega
    omega

/-- The alternating grade eigenvalues are distinct in even dimension. -/
theorem shirokov_even_grade_eigenvalues_injective {n : ℕ} (hn : Even n) :
    Function.Injective (fun i : Fin (n + 1) => shirokovGradeEigenvalue n i.val) := by
  intro i j hij
  change shirokovGradeEigenvalue n i.val = shirokovGradeEigenvalue n j.val at hij
  by_cases hiEven : Even i.val <;> by_cases hjEven : Even j.val
  · obtain ⟨a, ha⟩ := hiEven
    obtain ⟨b, hb⟩ := hjEven
    have hia : i.val = 2 * a := by omega
    have hjb : j.val = 2 * b := by omega
    have hpA : (-1 : ℤ) ^ (a + a) = 1 := by
      rw [← two_mul a, pow_mul]
      norm_num
    have hpB : (-1 : ℤ) ^ (b + b) = 1 := by
      rw [← two_mul b, pow_mul]
      norm_num
    rw [hia, hjb] at hij
    have heq : (n : ℤ) - 2 * ((2 * a : ℕ) : ℤ) =
        (n : ℤ) - 2 * ((2 * b : ℕ) : ℤ) := by
      simpa [shirokovGradeEigenvalue, hpA, hpB] using hij
    have : a = b := by omega
    apply Fin.ext
    omega
  · obtain ⟨a, ha⟩ := hiEven
    obtain ⟨b, hb⟩ := (Nat.not_even_iff_odd.mp hjEven)
    obtain ⟨c, hc⟩ := hn
    have hia : i.val = 2 * a := by omega
    have hjb : j.val = 2 * b + 1 := by omega
    have hpA : (-1 : ℤ) ^ (a + a) = 1 := by
      rw [← two_mul a, pow_mul]
      norm_num
    have hpB : (-1 : ℤ) ^ (b + b) = 1 := by
      rw [← two_mul b, pow_mul]
      norm_num
    have hpOdd : (-1 : ℤ) ^ (2 * b + 1) = -1 := by
      calc
        (-1 : ℤ) ^ (2 * b + 1) = (-1 : ℤ) ^ (2 * b) * (-1) := by
          rw [pow_succ]
        _ = (-1 : ℤ) ^ (b + b) * (-1) := by rw [show 2 * b = b + b by omega]
        _ = -1 := by rw [hpB]; norm_num
    rw [hia, hjb] at hij
    have hcontra : ((c : ℤ) + c) - 2 * ((2 * a : ℕ) : ℤ) =
        -(((c : ℤ) + c) - 2 * ((2 * b + 1 : ℕ) : ℤ)) := by
      simpa [shirokovGradeEigenvalue, hc, hpA, hpOdd] using hij
    have hiBound := i.isLt
    have hjBound := j.isLt
    omega
  · obtain ⟨a, ha⟩ := (Nat.not_even_iff_odd.mp hiEven)
    obtain ⟨b, hb⟩ := hjEven
    obtain ⟨c, hc⟩ := hn
    have hia : i.val = 2 * a + 1 := by omega
    have hjb : j.val = 2 * b := by omega
    have hpA : (-1 : ℤ) ^ (a + a) = 1 := by
      rw [← two_mul a, pow_mul]
      norm_num
    have hpB : (-1 : ℤ) ^ (b + b) = 1 := by
      rw [← two_mul b, pow_mul]
      norm_num
    have hpOdd : (-1 : ℤ) ^ (2 * a + 1) = -1 := by
      calc
        (-1 : ℤ) ^ (2 * a + 1) = (-1 : ℤ) ^ (2 * a) * (-1) := by
          rw [pow_succ]
        _ = (-1 : ℤ) ^ (a + a) * (-1) := by rw [show 2 * a = a + a by omega]
        _ = -1 := by rw [hpA]; norm_num
    rw [hia, hjb] at hij
    have hcontra : -(((c : ℤ) + c) - 2 * ((2 * a + 1 : ℕ) : ℤ)) =
        ((c : ℤ) + c) - 2 * ((2 * b : ℕ) : ℤ) := by
      simpa [shirokovGradeEigenvalue, hc, hpOdd, hpB] using hij
    have hiBound := i.isLt
    have hjBound := j.isLt
    omega
  · obtain ⟨a, ha⟩ := (Nat.not_even_iff_odd.mp hiEven)
    obtain ⟨b, hb⟩ := (Nat.not_even_iff_odd.mp hjEven)
    have hia : i.val = 2 * a + 1 := by omega
    have hjb : j.val = 2 * b + 1 := by omega
    have hpA : (-1 : ℤ) ^ (a + a) = 1 := by
      rw [← two_mul a, pow_mul]
      norm_num
    have hpB : (-1 : ℤ) ^ (b + b) = 1 := by
      rw [← two_mul b, pow_mul]
      norm_num
    have hpOddA : (-1 : ℤ) ^ (2 * a + 1) = -1 := by
      calc
        (-1 : ℤ) ^ (2 * a + 1) = (-1 : ℤ) ^ (2 * a) * (-1) := by
          rw [pow_succ]
        _ = (-1 : ℤ) ^ (a + a) * (-1) := by rw [show 2 * a = a + a by omega]
        _ = -1 := by rw [hpA]; norm_num
    have hpOddB : (-1 : ℤ) ^ (2 * b + 1) = -1 := by
      calc
        (-1 : ℤ) ^ (2 * b + 1) = (-1 : ℤ) ^ (2 * b) * (-1) := by
          rw [pow_succ]
        _ = (-1 : ℤ) ^ (b + b) * (-1) := by rw [show 2 * b = b + b by omega]
        _ = -1 := by rw [hpB]; norm_num
    rw [hia, hjb] at hij
    have heq : (n : ℤ) - 2 * ((2 * a + 1 : ℕ) : ℤ) =
        (n : ℤ) - 2 * ((2 * b + 1 : ℕ) : ℤ) := by
      simpa [shirokovGradeEigenvalue, hpOddA, hpOddB] using hij
    have : a = b := by omega
    apply Fin.ext
    omega

/-- In odd dimension, scalar and top-grade modes have the same sandwich
eigenvalue, explaining why this one operator cannot separate all grades. -/
theorem shirokov_odd_grade_eigenvalue_top_collision {n : ℕ} (hn : Odd n) :
    shirokovGradeEigenvalue n 0 = shirokovGradeEigenvalue n n := by
  obtain ⟨m, hm⟩ := hn
  have hpM : (-1 : ℤ) ^ (m + m) = 1 := by
    rw [← two_mul m, pow_mul]
    norm_num
  have hp : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
    calc
      (-1 : ℤ) ^ (2 * m + 1) = (-1 : ℤ) ^ (2 * m) * (-1) := by
        rw [pow_succ]
      _ = (-1 : ℤ) ^ (m + m) * (-1) := by
        rw [show 2 * m = m + m by omega]
      _ = 1 * (-1) := by rw [hpM]
      _ = -1 := by norm_num
  rw [shirokovGradeEigenvalue, shirokovGradeEigenvalue, hm, pow_zero, hp]
  push_cast
  ring

/-- In odd dimension, complementary grades have the same sandwich eigenvalue.
This strengthens the scalar/top-grade collision to every pair `k`, `n-k`. -/
theorem shirokov_odd_grade_eigenvalue_complement {n k : ℕ}
    (hn : Odd n) (hk : k ≤ n) :
    shirokovGradeEigenvalue n (n - k) = shirokovGradeEigenvalue n k := by
  obtain ⟨m, rfl⟩ := hn
  by_cases hkEven : Even k
  · obtain ⟨a, ha⟩ := hkEven
    have hka : k = 2 * a := by omega
    have hk' : 2 * a ≤ 2 * m + 1 := by simpa [hka] using hk
    have hbound : a ≤ m := by omega
    have hpowEven : (-1 : ℤ) ^ (2 * a) = 1 := by
      rw [show 2 * a = a + a by omega, pow_add]
      calc
        (-1 : ℤ) ^ a * (-1) ^ a = ((-1 : ℤ) * (-1)) ^ a :=
          (mul_pow _ _ _).symm
        _ = 1 := by norm_num
    have hpowOdd : (-1 : ℤ) ^ (2 * (m - a) + 1) = -1 := by
      rw [pow_succ]
      have heven : (-1 : ℤ) ^ (2 * (m - a)) = 1 := by
        rw [show 2 * (m - a) = (m - a) + (m - a) by omega, pow_add]
        calc
          (-1 : ℤ) ^ (m - a) * (-1) ^ (m - a) =
              ((-1 : ℤ) * (-1)) ^ (m - a) := (mul_pow _ _ _).symm
          _ = 1 := by norm_num
      rw [heven]
      norm_num
    have hcomp : 2 * m + 1 - k = 2 * (m - a) + 1 := by omega
    unfold shirokovGradeEigenvalue
    rw [hcomp, hka, hpowEven, hpowOdd]
    push_cast
    omega
  · have hkOdd : Odd k := (Nat.not_even_iff_odd.mp hkEven)
    obtain ⟨a, ha⟩ := hkOdd
    have hka : k = 2 * a + 1 := by omega
    have hk' : 2 * a + 1 ≤ 2 * m + 1 := by simpa [hka] using hk
    have hbound : a ≤ m := by omega
    have hpowEven : (-1 : ℤ) ^ (2 * (m - a)) = 1 := by
      rw [show 2 * (m - a) = (m - a) + (m - a) by omega, pow_add]
      calc
        (-1 : ℤ) ^ (m - a) * (-1) ^ (m - a) =
            ((-1 : ℤ) * (-1)) ^ (m - a) := (mul_pow _ _ _).symm
        _ = 1 := by norm_num
    have hpowOdd : (-1 : ℤ) ^ (2 * a + 1) = -1 := by
      rw [pow_succ]
      have heven : (-1 : ℤ) ^ (2 * a) = 1 := by
        rw [show 2 * a = a + a by omega, pow_add]
        calc
          (-1 : ℤ) ^ a * (-1) ^ a = ((-1 : ℤ) * (-1)) ^ a :=
            (mul_pow _ _ _).symm
          _ = 1 := by norm_num
      rw [heven]
      norm_num
    have hcomp : 2 * m + 1 - k = 2 * (m - a) := by omega
    unfold shirokovGradeEigenvalue
    rw [hcomp, hka, hpowEven, hpowOdd]
    push_cast
    omega

/-- The alternating grade eigenvalues are not injective in odd dimension. -/
theorem shirokov_odd_grade_eigenvalues_not_injective {n : ℕ} (hn : Odd n) :
    ¬ Function.Injective (fun i : Fin (n + 1) => shirokovGradeEigenvalue n i.val) := by
  intro hinj
  have hcollision :
      shirokovGradeEigenvalue n (0 : Fin (n + 1)).val =
        shirokovGradeEigenvalue n (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).val :=
    shirokov_odd_grade_eigenvalue_top_collision hn
  have heq := hinj hcollision
  have hnpos : 0 < n := by obtain ⟨m, hm⟩ := hn; omega
  have hne : (0 : Fin (n + 1)) ≠ ⟨n, Nat.lt_succ_self n⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  exact hne heq

/-- The power coefficient matrix in Shirokov's even-dimensional projection formula.
Its rows are powers and its columns correspond to the eigenvalues `λᵢ`. -/
def shirokovGradeProjectionMatrix (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  (Matrix.vandermonde
    (fun i : Fin (n + 1) => (shirokovGradeEigenvalue n i.val : ℚ))).transpose

/-- In even dimension the coefficient matrix `Aₙ₊₁` in (1.8) is nonsingular
over `ℚ`, hence has an inverse there. -/
theorem shirokov_even_grade_projection_matrix_det_ne_zero {n : ℕ} (hn : Even n) :
    (shirokovGradeProjectionMatrix n).det ≠ 0 := by
  rw [shirokovGradeProjectionMatrix, Matrix.det_transpose]
  exact (Matrix.det_vandermonde_ne_zero_iff).2
    (fun i j hij => by
      apply shirokov_even_grade_eigenvalues_injective hn
      exact_mod_cast hij)

/-- The Vandermonde determinant vanishes in odd dimension because its scalar
and top-grade columns coincide. -/
theorem shirokov_odd_grade_projection_matrix_det_eq_zero {n : ℕ} (hn : Odd n) :
    (shirokovGradeProjectionMatrix n).det = 0 := by
  rw [shirokovGradeProjectionMatrix, Matrix.det_transpose]
  apply Matrix.det_vandermonde_eq_zero_iff.mpr
  have hnpos : 0 < n := by obtain ⟨m, hm⟩ := hn; omega
  have hcollision :
      (shirokovGradeEigenvalue n 0 : ℚ) =
        (shirokovGradeEigenvalue n n : ℚ) := by
    exact_mod_cast shirokov_odd_grade_eigenvalue_top_collision hn
  refine ⟨0, ⟨n, Nat.lt_succ_self n⟩, ?_, ?_⟩
  · exact hcollision
  · intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega

/-- In odd dimension the explicit grade-projection coefficient matrix is not
invertible; the collision is a genuine rank obstruction. -/
theorem shirokov_odd_grade_projection_matrix_not_isUnit {n : ℕ} (hn : Odd n) :
    ¬ IsUnit (shirokovGradeProjectionMatrix n) := by
  intro hunit
  have hdet : IsUnit (shirokovGradeProjectionMatrix n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hne : (shirokovGradeProjectionMatrix n).det ≠ 0 :=
    isUnit_iff_ne_zero.mp hdet
  exact hne (shirokov_odd_grade_projection_matrix_det_eq_zero hn)

/-- The even-dimensional coefficient matrix in (1.8) is invertible over
`ℚ`; the theorem is about the explicit finite power matrix, not yet the
Clifford-valued projection identity. -/
theorem shirokov_even_grade_projection_matrix_isUnit {n : ℕ} (hn : Even n) :
    IsUnit (shirokovGradeProjectionMatrix n) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (shirokov_even_grade_projection_matrix_det_ne_zero hn)

/-- Vandermonde matrix for the eigenvalues of the standard-frame sandwich on
the fixed negative-definite carrier. -/
def shirokovSandwichPowerMatrix (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.vandermonde (fun i : Fin (n + 1) =>
    -(shirokovGradeEigenvalue n i.val : ℚ))

/-- The sandwich power matrix is invertible for even dimension. -/
theorem shirokov_even_sandwich_power_matrix_isUnit {n : ℕ} (hn : Even n) :
    IsUnit (shirokovSandwichPowerMatrix n) := by
  rw [shirokovSandwichPowerMatrix, Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  apply shirokov_even_grade_eigenvalues_injective hn
  exact_mod_cast (neg_injective hij)

/-- The inverse Vandermonde coefficients interpolate the Kronecker delta on
the sandwich eigenvalues. This is the scalar grade-isolation step in (1.8). -/
theorem shirokov_even_grade_scalar_interpolation {n : ℕ} (hn : Even n)
    (i k : Fin (n + 1)) :
    (∑ j : Fin (n + 1),
      (-(shirokovGradeEigenvalue n i.val : ℚ)) ^ (j : ℕ) *
        (shirokovSandwichPowerMatrix n)⁻¹ j k) = if i = k then 1 else 0 := by
  have hdet : IsUnit (shirokovSandwichPowerMatrix n).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (shirokov_even_sandwich_power_matrix_isUnit hn)
  have hinv := Matrix.mul_nonsing_inv (shirokovSandwichPowerMatrix n) hdet
  have hentry := congrFun (congrFun hinv i) k
  simpa [shirokovSandwichPowerMatrix, Matrix.mul_apply, Matrix.vandermonde,
    Matrix.one_apply] using hentry

/-- Real coefficient matrix for the same interpolation, used to form an
endomorphism of the real Clifford algebra. -/
def shirokovSandwichPowerMatrixReal (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.vandermonde (fun i : Fin (n + 1) =>
    -(shirokovGradeEigenvalue n i.val : ℝ))

theorem shirokov_even_sandwich_power_matrix_real_isUnit {n : ℕ} (hn : Even n) :
    IsUnit (shirokovSandwichPowerMatrixReal n) := by
  rw [shirokovSandwichPowerMatrixReal, Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  apply shirokov_even_grade_eigenvalues_injective hn
  exact_mod_cast (neg_injective hij)

theorem shirokov_even_grade_real_scalar_interpolation {n : ℕ} (hn : Even n)
    (i k : Fin (n + 1)) :
    (∑ j : Fin (n + 1),
      (-(shirokovGradeEigenvalue n i.val : ℝ)) ^ (j : ℕ) *
        (shirokovSandwichPowerMatrixReal n)⁻¹ j k) = if i = k then 1 else 0 := by
  have hdet : IsUnit (shirokovSandwichPowerMatrixReal n).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (shirokov_even_sandwich_power_matrix_real_isUnit hn)
  have hinv := Matrix.mul_nonsing_inv (shirokovSandwichPowerMatrixReal n) hdet
  have hentry := congrFun (congrFun hinv i) k
  simpa [shirokovSandwichPowerMatrixReal, Matrix.mul_apply,
    Matrix.vandermonde, Matrix.one_apply] using hentry

/-- Shirokov's standard-frame sandwich operator on the negative-definite
finite-stage algebra `Cl(0,n)`. -/
def shirokovGradeSandwich (n : ℕ)
    (U : CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
  ∑ a : Fin n, cGen ℝ n a * U * cGen ℝ n a

/-- A single generator sandwich acts diagonally on an ordered blade; the sign
depends on the blade grade and whether the generator belongs to the blade. -/
theorem shirokov_generator_sandwich_blade (n : ℕ) (a : Fin n)
    (S : Finset (Fin n)) :
    cGen ℝ n a * cBlade ℝ n S * cGen ℝ n a =
      -((-1 : ℝ) ^ (S.card + if a ∈ S then 1 else 0)) • cBlade ℝ n S := by
  rw [cGen_mul_cBlade]
  rw [smul_mul_assoc, mul_assoc, cGen_sq]
  simp

/-- The full standard-frame sandwich operator acts by a scalar on every
ordered blade; the next step is to evaluate this scalar as `λ_|S|`. -/
theorem shirokov_grade_sandwich_blade_scalar (n : ℕ) (S : Finset (Fin n)) :
    shirokovGradeSandwich n (cBlade ℝ n S) =
      (∑ a : Fin n,
        -((-1 : ℝ) ^ (S.card + if a ∈ S then 1 else 0))) • cBlade ℝ n S := by
  simp only [shirokovGradeSandwich]
  simp_rw [shirokov_generator_sandwich_blade]
  rw [← Finset.sum_smul]

/-- The scalar of the frame sandwich on a grade-`k` blade is the negative
of Shirokov's eigenvalue `λₖ = (-1)^k (n - 2k)`. -/
theorem shirokov_grade_sandwich_blade_eigenvalue (n : ℕ)
    (S : Finset (Fin n)) :
    (∑ a : Fin n,
      -((-1 : ℝ) ^ (S.card + if a ∈ S then 1 else 0))) =
        -(shirokovGradeEigenvalue n S.card : ℝ) := by
  have hterm : ∀ a : Fin n,
      -((-1 : ℝ) ^ (S.card + if a ∈ S then 1 else 0)) =
        (-1 : ℝ) ^ S.card * (2 * (if a ∈ S then 1 else 0) - 1) := by
    intro a
    by_cases ha : a ∈ S <;> simp [ha, pow_succ] <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  have hmem : (∑ a : Fin n, (if a ∈ S then (1 : ℝ) else 0)) = S.card := by
    rw [Finset.sum_boole]
    simp
  have hconst : (∑ a : Fin n, (1 : ℝ)) = n := by simp
  have htwice : (∑ a : Fin n, 2 * (if a ∈ S then (1 : ℝ) else 0)) =
      2 * S.card := by rw [← Finset.mul_sum, hmem]
  rw [htwice, hconst]
  unfold shirokovGradeEigenvalue
  push_cast
  ring

/-- The standard-frame sandwich has the paper's grade eigenvalue on each
ordered blade, with a minus sign from the negative Clifford generator square. -/
theorem shirokov_grade_sandwich_blade_eigenvalue_action (n : ℕ)
    (S : Finset (Fin n)) :
    shirokovGradeSandwich n (cBlade ℝ n S) =
      (-(shirokovGradeEigenvalue n S.card : ℝ)) • cBlade ℝ n S := by
  rw [shirokov_grade_sandwich_blade_scalar,
    shirokov_grade_sandwich_blade_eigenvalue]

/-- The frame sandwich as a real-linear endomorphism of the same Clifford
algebra, so its polynomial spectral projections retain the full carrier. -/
def shirokovGradeSandwichLinear (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) →ₗ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ n) where
  toFun := shirokovGradeSandwich n
  map_add' x y := by
    unfold shirokovGradeSandwich
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    unfold shirokovGradeSandwich
    simp_rw [mul_smul_comm, smul_mul_assoc]
    rw [Finset.smul_sum]
    simp

theorem shirokov_sandwich_power_blade (n : ℕ) (S : Finset (Fin n))
    (j : ℕ) :
    (shirokovGradeSandwichLinear n ^ j) (cBlade ℝ n S) =
      (-(shirokovGradeEigenvalue n S.card : ℝ)) ^ j • cBlade ℝ n S := by
  let μ : ℝ := -(shirokovGradeEigenvalue n S.card : ℝ)
  have hbase : shirokovGradeSandwichLinear n (cBlade ℝ n S) =
      μ • cBlade ℝ n S := by
    exact shirokov_grade_sandwich_blade_eigenvalue_action n S
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, hbase, map_smul, ih]
    calc
      μ • (-shirokovGradeEigenvalue n S.card : ℝ) ^ j • cBlade ℝ n S =
          (μ * (-shirokovGradeEigenvalue n S.card : ℝ) ^ j) • cBlade ℝ n S :=
        smul_smul _ _ _
      _ = (-shirokovGradeEigenvalue n S.card : ℝ) ^ (j + 1) •
          cBlade ℝ n S := by rw [pow_succ]; congr 1 <;> dsimp [μ] <;> ring

/-- Polynomial spectral projection onto the `k`th sandwich eigenspace, acting
on the Clifford algebra itself. -/
def shirokovGradeProjector (n : ℕ) (k : Fin (n + 1)) :
    Module.End ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
  ∑ j : Fin (n + 1),
    ((shirokovSandwichPowerMatrixReal n)⁻¹ j k) •
      (shirokovGradeSandwichLinear n) ^ (j : ℕ)

/-- The polynomial projector selects exactly the ordered blades of grade `k`.
This lifts scalar Vandermonde interpolation to the full finite-stage Clifford
carrier by its native ordered-blade basis. -/
theorem shirokov_even_grade_projector_blade {n : ℕ} (hn : Even n)
    (k : Fin (n + 1)) (S : Finset (Fin n)) :
    shirokovGradeProjector n k (cBlade ℝ n S) =
      (if (⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩ :
          Fin (n + 1)) = k then (1 : ℝ) else 0) • cBlade ℝ n S := by
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  let iS : Fin (n + 1) := ⟨S.card, Nat.lt_succ_of_le hcard⟩
  have hinterp := shirokov_even_grade_real_scalar_interpolation hn iS k
  have hsum : (∑ j : Fin (n + 1),
      (shirokovSandwichPowerMatrixReal n)⁻¹ j k *
        (-(shirokovGradeEigenvalue n S.card : ℝ)) ^ (j : ℕ)) =
      if iS = k then 1 else 0 := by
    have hcomm : (∑ j : Fin (n + 1),
        (shirokovSandwichPowerMatrixReal n)⁻¹ j k *
          (-(shirokovGradeEigenvalue n S.card : ℝ)) ^ (j : ℕ)) =
        ∑ j : Fin (n + 1),
          (-(shirokovGradeEigenvalue n S.card : ℝ)) ^ (j : ℕ) *
            (shirokovSandwichPowerMatrixReal n)⁻¹ j k := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hinterp' : (∑ j : Fin (n + 1),
        (-(shirokovGradeEigenvalue n S.card : ℝ)) ^ (j : ℕ) *
          (shirokovSandwichPowerMatrixReal n)⁻¹ j k) = if iS = k then 1 else 0 := by
      simpa [iS] using hinterp
    exact hcomm.trans hinterp'
  simp only [shirokovGradeProjector, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simp_rw [shirokov_sandwich_power_blade, smul_smul]
  rw [← Finset.sum_smul, hsum]

/-- The first two generators in the concrete negative-definite `Cl(0,2)`. -/
private def shirokovWitnessGen0 :
    CliffordAlgebra (cliffordNegSqForm ℝ 2) := cGen ℝ 2 0

private def shirokovWitnessGen1 :
    CliffordAlgebra (cliffordNegSqForm ℝ 2) := cGen ℝ 2 1

/-- Distinct orthogonal Clifford generators do not commute. -/
theorem shirokov_generators_noncommute :
    shirokovWitnessGen0 * shirokovWitnessGen1 ≠
      shirokovWitnessGen1 * shirokovWitnessGen0 := by
  exact cGen_noncomm ℝ (by norm_num) (by decide)

/-- A Clifford frame with at least two members has no central frame vector.
The square and orthogonality relations alone imply this noncentrality
conclusion; Shirokov's odd-volume trace condition is needed for the separate
basis-independence claim. -/
theorem shirokov_frame_vectors_noncentral {B : Type*} [Ring B] [Algebra ℝ B]
    [Nontrivial B] [NoZeroSMulDivisors ℝ B]
    (m : ℕ) (h : Fin (m + 2) → B) (ε : Fin (m + 2) → ℝ)
    (hε : ∀ i, ε i ≠ 0)
    (hsq : ∀ i, h i * h i = ε i • (1 : B))
    (hanti : ∀ i j, i ≠ j → h i * h j + h j * h i = 0) :
    ∀ i, ¬ (∀ y, h i * y = y * h i) := by
  intro i hcentral
  have hcard : 1 < Fintype.card (Fin (m + 2)) := by simp
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  have hcomm : h i * h j = h j * h i := hcentral (h j)
  have hsum := hanti j i hji
  have hdouble : h i * h j + h i * h j = 0 := by simpa [hcomm] using hsum
  have hprod : h i * h j = 0 := by
    have hmul : (2 : ℝ) • (h i * h j) = 0 := by simpa [two_smul] using hdouble
    exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hscaled : ε i • h j = 0 := by
    calc
      ε i • h j = (h i * h i) * h j := by rw [hsq i]; simp
      _ = h i * (h i * h j) := by rw [mul_assoc]
      _ = 0 := by rw [hprod]; simp
  have hjzero : h j = 0 := (smul_eq_zero.mp hscaled).resolve_left (hε i)
  have hsqj := hsq j
  rw [hjzero] at hsqj
  simp only [zero_mul] at hsqj
  exact (smul_ne_zero (hε j) one_ne_zero) hsqj.symm

/-- The real-linear map underlying conjugation by a unit, used to transport a
connection one-form without commuting its coefficient algebra. -/
def shirokovFrameTransportLinear {A : Type*} [Ring A] [Algebra ℝ A]
    (g : Aˣ) : A →ₗ[ℝ] A where
  toFun := frameTransport g
  map_add' a b := by simp [frameTransport, mul_add, add_mul]
  map_smul' r a := by
    simp [frameTransport, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

/-- Shirokov's transformed connection in the covariant-derivative convention
`D + [Γ, ·]`: it is `g⁻¹ Dg - g⁻¹ C g`, the negative of the paper's `C'`. -/
def shirokovGaugeCovariantForm {A : Type*} [Ring A] [Algebra ℝ A]
    (K : DerivationLieLane ℝ A) (g : Aˣ) (C : OneForm K) : OneForm K :=
  gaugeForm K g - shirokovFrameTransportLinear g ∘ₗ C

/-- Gauge covariance of the compatibility operator in Shirokov's Theorem 1.2.
For arbitrary noncommutative coefficients, conjugating `a` and transforming
`C` by the paper's rule transports the full residual `D a - [C,a]`. -/
theorem shirokov_theorem_1_2_gauge_covariance
    {A : Type*} [Ring A] [Algebra ℝ A]
    (K : DerivationLieLane ℝ A) (g : Aˣ) (C : OneForm K)
    (x : K.L) (a : A) :
    covariantDerivative K (shirokovGaugeCovariantForm K g C) x
        (frameTransport g a) =
      frameTransport g
        (K.operatorAction x a - (C x * a - a * C x)) := by
  let a' := frameTransport g a
  let θ := gaugeForm K g x
  let c' := frameTransport g (C x)
  have hframe : K.operatorAction x a' + θ * a' - a' * θ =
      frameTransport g (K.operatorAction x a) := by
    simpa [a', θ, covariantDerivative] using covariant_frameTransport K g x a
  have hcomm : c' * a' - a' * c' =
      frameTransport g (C x * a - a * C x) := by
    calc
      c' * a' - a' * c' = frameTransport g (C x * a) -
          frameTransport g (a * C x) := by
            rw [← frameTransport_mul, ← frameTransport_mul]
      _ = frameTransport g (C x * a - a * C x) := by
            exact (map_sub (shirokovFrameTransportLinear g)
              (C x * a) (a * C x)).symm
  change K.operatorAction x a' + (θ - c') * a' - a' * (θ - c') = _
  calc
    _ = (K.operatorAction x a' + θ * a' - a' * θ) - (c' * a' - a' * c') := by
      noncomm_ring
    _ = frameTransport g (K.operatorAction x a) -
        frameTransport g (C x * a - a * C x) := by rw [hframe, hcomm]
    _ = frameTransport g
        (K.operatorAction x a - (C x * a - a * C x)) := by
      exact (map_sub (shirokovFrameTransportLinear g)
        (K.operatorAction x a) (C x * a - a * C x)).symm

/-- A coordinate generator after an isometric change of frame in `Cl(0,n)`. -/
def shirokovIsometryFrameVector (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (i : Fin n) : CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  CliffordAlgebra.ι (cliffordNegSqForm ℝ n) (e (Pi.single i (1 : ℝ)))

/-- The ascending ordered blade in the isometry-transformed frame. -/
def shirokovIsometryFrameBlade (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) : CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  ((bladeList S).map (shirokovIsometryFrameVector n e)).prod

@[simp] theorem shirokovIsometryFrameVector_sq (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (i : Fin n) :
    shirokovIsometryFrameVector n e i * shirokovIsometryFrameVector n e i = -1 := by
  have h := congrArg (CliffordAlgebra.equivOfIsometry e) (cGen_sq ℝ n i)
  simpa [shirokovIsometryFrameVector, cGen] using h

theorem shirokovIsometryFrameVector_anticommute (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    {i j : Fin n} (hij : i ≠ j) :
    shirokovIsometryFrameVector n e i * shirokovIsometryFrameVector n e j +
      shirokovIsometryFrameVector n e j * shirokovIsometryFrameVector n e i = 0 := by
  have h := congrArg (CliffordAlgebra.equivOfIsometry e) (cGen_mul_swap hij)
  simpa [shirokovIsometryFrameVector, cGen] using h

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The commutator convention used in Shirokov's compatibility equation. -/
private def algebraCommutator {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

private theorem derivation_map_commutator {A : Type*} [Ring A]
    (D : A →+ A) (hDmul : ∀ x y, D (x * y) = D x * y + x * D y)
    (x y : A) :
    D (algebraCommutator x y) =
      algebraCommutator (D x) y + algebraCommutator x (D y) := by
  simp only [algebraCommutator, map_sub, hDmul]
  noncomm_ring

/-- Compatibility with two commuting derivations forces the curvature defect
to commute with every coefficient. This is the algebraic consequence of
equation (1.7); concluding that the defect vanishes additionally requires a
center/grade argument. -/
theorem shirokov_compatibility_curvature_central
    {A : Type*} [Ring A]
    (D₁ D₂ : A →+ A) (C₁ C₂ : A)
    (hD₁mul : ∀ x y, D₁ (x * y) = D₁ x * y + x * D₁ y)
    (hD₂mul : ∀ x y, D₂ (x * y) = D₂ x * y + x * D₂ y)
    (hcomm : ∀ x, D₁ (D₂ x) = D₂ (D₁ x))
    (hcompat₁ : ∀ x, D₁ x = algebraCommutator C₁ x)
    (hcompat₂ : ∀ x, D₂ x = algebraCommutator C₂ x) :
    ∀ x, algebraCommutator
      (D₁ C₂ - D₂ C₁ - algebraCommutator C₁ C₂) x = 0 := by
  intro x
  have h := hcomm x
  rw [hcompat₂ x, derivation_map_commutator D₁ hD₁mul C₂ x,
    hcompat₁ x, derivation_map_commutator D₂ hD₂mul C₁ x,
    hcompat₂ x] at h
  calc
    algebraCommutator
        (D₁ C₂ - D₂ C₁ - algebraCommutator C₁ C₂) x =
        (D₁ C₂ * x - x * D₁ C₂ +
          (C₂ * (C₁ * x - x * C₁) - (C₁ * x - x * C₁) * C₂)) -
        (D₂ C₁ * x - x * D₂ C₁ +
          (C₁ * (C₂ * x - x * C₂) - (C₂ * x - x * C₂) * C₁)) := by
            dsimp [algebraCommutator]
            noncomm_ring
    _ = 0 := sub_eq_zero.mpr h

/-- Shirokov's compatibility equation on Clifford-vector generators implies
centrality of the coordinate curvature defect when the derivation directions
commute. The conclusion is centrality; eliminating the Clifford center still
requires the paper's grade restriction. -/
theorem shirokov_clifford_compatibility_curvature_central
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M)
    (K : DerivationLieLane ℝ (CliffordAlgebra Q))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : M,
      covariantDerivative K (-C) x (CliffordAlgebra.ι Q v) = 0)
    (hgen₂ : ∀ v : M,
      covariantDerivative K (-C) y (CliffordAlgebra.ι Q v) = 0) :
    ∀ a : CliffordAlgebra Q,
      algebraCommutator
        (K.operatorAction x (C y) - K.operatorAction y (C x) -
          algebraCommutator (C x) (C y)) a = 0 := by
  have hparallel₁ := covariantDerivative_zero_of_clifford_generators
    (Q := Q) (Kcl := K) (-C) x hgen₁
  have hparallel₂ := covariantDerivative_zero_of_clifford_generators
    (Q := Q) (Kcl := K) (-C) y hgen₂
  have hcompat₁ : ∀ a : CliffordAlgebra Q,
      K.operatorAction x a = algebraCommutator (C x) a := by
    intro a
    have h : K.operatorAction x a + -(C x * a) + a * C x = 0 := by
      simpa [covariantDerivative] using hparallel₁ a
    have h' : K.operatorAction x a = C x * a + -(a * C x) := by
      calc
        K.operatorAction x a =
            (K.operatorAction x a + -(C x * a) + a * C x) +
              (C x * a + -(a * C x)) := by abel
        _ = C x * a + -(a * C x) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  have hcompat₂ : ∀ a : CliffordAlgebra Q,
      K.operatorAction y a = algebraCommutator (C y) a := by
    intro a
    have h : K.operatorAction y a + -(C y * a) + a * C y = 0 := by
      simpa [covariantDerivative] using hparallel₂ a
    have h' : K.operatorAction y a = C y * a + -(a * C y) := by
      calc
        K.operatorAction y a =
            (K.operatorAction y a + -(C y * a) + a * C y) +
              (C y * a + -(a * C y)) := by abel
        _ = C y * a + -(a * C y) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  have hcomm : ∀ a : CliffordAlgebra Q,
      K.operatorAction x (K.operatorAction y a) =
        K.operatorAction y (K.operatorAction x a) := by
    intro a
    have h := K.operatorAction_commutator_apply x y a
    rw [hxy] at h
    simp only [map_zero, LinearMap.zero_apply] at h
    exact sub_eq_zero.mp h.symm
  exact shirokov_compatibility_curvature_central
    (K.operatorAction x).toAddMonoidHom
    (K.operatorAction y).toAddMonoidHom (C x) (C y)
    (fun a b => K.operatorAction_leibniz x a b)
    (fun a b => K.operatorAction_leibniz y a b)
    hcomm hcompat₁ hcompat₂

/-- Under the file's compatibility convention
`Dᵢ a = [Cᵢ,a]`, the curvature-defect expression reduces algebraically to
`[C₁,C₂]`. Generator compatibility suffices because the covariant derivative
is a derivation on the Clifford algebra. -/
theorem shirokov_curvature_defect_eq_connection_commutator
    {n : ℕ}
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
        algebraCommutator (C x) (C y) = algebraCommutator (C x) (C y) := by
  have hparallel₁ := covariantDerivative_zero_of_clifford_generators
    (Q := cliffordNegSqForm ℝ n) (Kcl := K) (-C) x hgen₁
  have hparallel₂ := covariantDerivative_zero_of_clifford_generators
    (Q := cliffordNegSqForm ℝ n) (Kcl := K) (-C) y hgen₂
  have hcompat₁ : ∀ a : CliffordAlgebra (cliffordNegSqForm ℝ n),
      K.operatorAction x a = algebraCommutator (C x) a := by
    intro a
    have h : K.operatorAction x a + -(C x * a) + a * C x = 0 := by
      simpa [covariantDerivative] using hparallel₁ a
    have h' : K.operatorAction x a = C x * a + -(a * C x) := by
      calc
        K.operatorAction x a =
            (K.operatorAction x a + -(C x * a) + a * C x) +
              (C x * a + -(a * C x)) := by abel
        _ = C x * a + -(a * C x) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  have hcompat₂ : ∀ a : CliffordAlgebra (cliffordNegSqForm ℝ n),
      K.operatorAction y a = algebraCommutator (C y) a := by
    intro a
    have h : K.operatorAction y a + -(C y * a) + a * C y = 0 := by
      simpa [covariantDerivative] using hparallel₂ a
    have h' : K.operatorAction y a = C y * a + -(a * C y) := by
      calc
        K.operatorAction y a =
            (K.operatorAction y a + -(C y * a) + a * C y) +
              (C y * a + -(a * C y)) := by abel
        _ = C y * a + -(a * C y) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  rw [hcompat₁ (C y), hcompat₂ (C x)]
  dsimp [algebraCommutator]
  noncomm_ring

/-- Shirokov Theorem 2.1 on an ordered frame: compatibility on each frame
generator propagates to every ordered product, with no commutativity assumption
on the coefficient algebra. -/
theorem shirokov_theorem_2_1_ordered_frame_products
    {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (C : OneForm K) (x : K.L)
    (frame : ι → A)
    (hframe : ∀ i : ι,
      covariantDerivative K (-C) x (frame i) = 0) :
    ∀ word : List ι,
      K.operatorAction x ((word.map frame).prod) =
        algebraCommutator (C x) ((word.map frame).prod) := by
  intro word
  have hprod := covariantDerivative_list_prod_zero K (-C) x
    (word.map frame) (by
      intro a ha
      rcases List.mem_map.mp ha with ⟨i, hi, hEq⟩
      subst a
      exact hframe i)
  have h : K.operatorAction x ((word.map frame).prod) +
      -(C x * (word.map frame).prod) + (word.map frame).prod * C x = 0 := by
    simpa [covariantDerivative] using hprod
  have h' : K.operatorAction x ((word.map frame).prod) =
      C x * (word.map frame).prod + -((word.map frame).prod * C x) := by
    calc
      K.operatorAction x ((word.map frame).prod) =
          (K.operatorAction x ((word.map frame).prod) +
            -(C x * (word.map frame).prod) + (word.map frame).prod * C x) +
            (C x * (word.map frame).prod + -((word.map frame).prod * C x)) := by
              abel
      _ = C x * (word.map frame).prod + -((word.map frame).prod * C x) := by
            rw [h]
            simp
  simpa [algebraCommutator, sub_eq_add_neg] using h'

/-- The final algebraic reduction in Shirokov's Theorem 2.2. For an indexed
dual frame, compatibility and the stated Reynolds average imply the averaged
connection formula modulo the center projection. The Clifford-specific
Reynolds identity and the fact that the connection has zero center component
are separate obligations. -/
theorem shirokov_theorem_2_2_average_reduction
    {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A] [Fintype ι]
    (D : A → A) (C : A) (centerProj : A → A) (frame : ι → Aˣ)
    (hcompat : ∀ i, D (frame i : A) =
      C * (frame i : A) - (frame i : A) * C)
    (haverage : ∑ i : ι,
      (frame i : A) * C * (↑((frame i)⁻¹) : A) =
        Fintype.card ι • centerProj C) :
    ∑ i : ι, D (frame i : A) * (↑((frame i)⁻¹) : A) =
      Fintype.card ι • (C - centerProj C) := by
  have hterm (i : ι) :
      D (frame i : A) * (↑((frame i)⁻¹) : A) =
        C - (frame i : A) * C * (↑((frame i)⁻¹) : A) := by
    rw [hcompat i]
    have hu : (frame i : A) * (↑((frame i)⁻¹) : A) = 1 := by simp
    calc
      (C * (frame i : A) - (frame i : A) * C) *
          (↑((frame i)⁻¹) : A) =
        C * ((frame i : A) * (↑((frame i)⁻¹) : A)) -
          (frame i : A) * C * (↑((frame i)⁻¹) : A) := by noncomm_ring
      _ = C - (frame i : A) * C * (↑((frame i)⁻¹) : A) := by rw [hu, mul_one]
  calc
    ∑ i : ι, D (frame i : A) * (↑((frame i)⁻¹) : A) =
        ∑ i : ι, (C - (frame i : A) * C * (↑((frame i)⁻¹) : A)) := by
          exact Finset.sum_congr rfl fun i _ => hterm i
    _ = (∑ _i : ι, C) -
        ∑ i : ι, (frame i : A) * C * (↑((frame i)⁻¹) : A) := by
          rw [Finset.sum_sub_distrib]
    _ = Fintype.card ι • C - Fintype.card ι • centerProj C := by
          rw [Finset.sum_const, Finset.card_univ, haverage]
    _ = Fintype.card ι • (C - centerProj C) := by rw [nsmul_sub]

/-- The Clifford blade swap law gives an explicit conjugation coefficient.
This is the finite combinatorial input needed for the standard-frame Reynolds
average; it is stated for the repository's negative-definite `Cl(0,n)` blade
owner and does not yet identify the average with the center projection. -/
theorem shirokov_blade_conjugation_sign
    {R : Type*} [CommRing R] (n : ℕ) (S T : Finset (Fin n)) :
    cBlade R n S * cBlade R n T * cBlade R n S =
      ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
        S.card * (S.card + 1) / 2)) • cBlade R n T := by
  obtain ⟨_, hswap⟩ := cBlade_mul_swap_overlap R n S T
  calc
    cBlade R n S * cBlade R n T * cBlade R n S =
        (cBlade R n S * cBlade R n T) * cBlade R n S := by noncomm_ring
    _ = (((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
        (cBlade R n T * cBlade R n S)) * cBlade R n S := by rw [hswap]
    _ = ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
        (cBlade R n T * (cBlade R n S * cBlade R n S)) := by
          rw [smul_mul_assoc]; congr 1; noncomm_ring
    _ = ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
        (((-1 : R) ^ (S.card * (S.card + 1) / 2)) • cBlade R n T) := by
          rw [cBlade_sq, mul_smul_comm, mul_one]
    _ = ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
          S.card * (S.card + 1) / 2)) • cBlade R n T := by
          calc
            _ = (((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) *
                (-1 : R) ^ (S.card * (S.card + 1) / 2)) • cBlade R n T :=
                  smul_smul _ _ _
            _ = _ := by rw [← pow_add]

/-- The Reynolds character sum factors as a coordinatewise product. This is
the combinatorial cancellation mechanism for the standard blade frame; a
separate parity lemma identifies these factors with the conjugation signs. -/
theorem shirokov_reynolds_character_sum (n : ℕ) (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)) =
      ∏ i ∈ (Finset.univ : Finset (Fin n)),
        (1 + (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)) := by
  simpa using (Finset.prod_one_add
    (f := fun i : Fin n => (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0))
    (Finset.univ : Finset (Fin n))).symm

/-- Every noncentral blade character has zero standard-frame average: an even
nonempty blade is killed at a coordinate in it; an odd non-top blade is killed
at a coordinate outside it. -/
theorem shirokov_noncentral_blade_character_vanishes (n : ℕ)
    (T : Finset (Fin n))
    (hcase : (Even T.card ∧ T.Nonempty) ∨ (Odd T.card ∧
      T ≠ (Finset.univ : Finset (Fin n)))) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)) = 0 := by
  rw [shirokov_reynolds_character_sum]
  obtain hEven | hOdd := hcase
  · obtain ⟨i, hi⟩ := hEven.2
    have hfactor : 1 + (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) = 0 := by
      obtain ⟨k, hk⟩ := hEven.1
      simp [hi, hk]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor
  · have hout : ∃ i : Fin n, i ∉ T := by
      by_contra h
      push Not at h
      apply hOdd.2
      ext i
      simp only [Finset.mem_univ]
      exact ⟨fun _ => trivial, fun _ => h i⟩
    obtain ⟨i, hi⟩ := hout
    have hfactor : 1 + (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) = 0 := by
      obtain ⟨k, hk⟩ := hOdd.1
      simp [hi, hk, pow_add, pow_mul]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor

/-- The product character is exactly the sign from swapping two Clifford
blades; `k^2` and `k` have the same parity for the overlap cardinality `k`. -/
theorem shirokov_blade_character_product (n : ℕ)
    (S T : Finset (Fin n)) :
    ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) =
      (-1 : ℤ) ^ (S.card * T.card + (S ∩ T).card) := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum :
      (∑ i ∈ S, (T.card + if i ∈ T then 1 else 0)) =
        S.card * T.card + (S ∩ T).card := by
    simp [Finset.sum_add_distrib, Finset.sum_const]
  rw [hsum]

/-- The overlap exponent in the Clifford blade swap law is the same sign
character that factors over coordinates in the standard-frame average. -/
theorem shirokov_blade_swap_sign_character (n : ℕ)
    (S T : Finset (Fin n)) :
    (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2) =
      ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) := by
  have hle := (cBlade_mul_swap_overlap ℤ n S T).1
  have hmod : S.card * T.card - (S ∩ T).card ^ 2 ≡
      S.card * T.card + (S ∩ T).card [MOD 2] := by
    have hk : (S ∩ T).card ^ 2 + (S ∩ T).card =
        (S ∩ T).card * ((S ∩ T).card + 1) := by ring
    have heven : 2 ∣ (S ∩ T).card * ((S ∩ T).card + 1) := by
      rcases Nat.even_or_odd (S ∩ T).card with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j * ((S ∩ T).card + 1), by rw [hj]; ring⟩
      · exact ⟨(S ∩ T).card * (j + 1), by rw [hj]; ring⟩
    rw [Nat.ModEq]
    omega
  rw [neg_one_pow_eq_of_modEq (R := ℤ) hmod,
    shirokov_blade_character_product]

/-- In `Cl(0,n)`, the ordered blade inverse is its square sign times itself. -/
theorem shirokov_blade_inverse_formula (n : ℕ) (S : Finset (Fin n)) :
    let b := cBlade ℝ n S
    let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
    (ε • b) * b = 1 ∧ b * (ε • b) = 1 := by
  dsimp
  let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
  have hε : ε * ε = 1 := by
    calc
      ε * ε = (-1 : ℝ) ^
          (S.card * (S.card + 1) / 2 + S.card * (S.card + 1) / 2) := by
            dsimp [ε]
            rw [← pow_add]
      _ = (-1 : ℝ) ^ (2 * (S.card * (S.card + 1) / 2)) := by
            congr 1 <;> omega
      _ = ((-1 : ℝ) ^ 2) ^ (S.card * (S.card + 1) / 2) := by rw [pow_mul]
      _ = 1 := by norm_num
  have hsq : cBlade ℝ n S * cBlade ℝ n S = ε • (1 : CliffordAlgebra
      (cliffordNegSqForm ℝ n)) := by
    simpa [ε] using cBlade_sq ℝ n S
  constructor
  · calc
      (ε • cBlade ℝ n S) * cBlade ℝ n S =
          ε • (cBlade ℝ n S * cBlade ℝ n S) := smul_mul_assoc _ _ _
      _ = ε • (ε • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n))) := by rw [hsq]
      _ = (ε * ε) • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n)) := smul_smul _ _ _
      _ = 1 := by rw [hε]; simp
  · calc
      cBlade ℝ n S * (ε • cBlade ℝ n S) =
          ε • (cBlade ℝ n S * cBlade ℝ n S) := mul_smul_comm _ _ _
      _ = ε • (ε • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n))) := by rw [hsq]
      _ = (ε * ε) • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n)) := smul_smul _ _ _
      _ = 1 := by rw [hε]; simp

/-- Conjugation by the actual inverse blade acts by the overlap sign, with the
blade-square sign canceled. -/
theorem shirokov_inverse_blade_conjugation_sign (n : ℕ)
    (S T : Finset (Fin n)) :
    let b := cBlade ℝ n S
    let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
    (ε • b) * cBlade ℝ n T * b =
      ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
  dsimp
  let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
  have hconj := shirokov_blade_conjugation_sign (R := ℝ) n S T
  calc
    (ε • cBlade ℝ n S) * cBlade ℝ n T * cBlade ℝ n S =
        ε • (cBlade ℝ n S * cBlade ℝ n T * cBlade ℝ n S) := by
          simp only [smul_mul_assoc]
    _ = ε • (((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
          S.card * (S.card + 1) / 2)) • cBlade ℝ n T) := by rw [hconj]
    _ = (ε * (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
          S.card * (S.card + 1) / 2)) • cBlade ℝ n T := smul_smul _ _ _
    _ = ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
          dsimp [ε]
          rw [← pow_add]
          have hmod : S.card * (S.card + 1) / 2 +
              (S.card * T.card - (S ∩ T).card ^ 2 +
                S.card * (S.card + 1) / 2) ≡
              S.card * T.card - (S ∩ T).card ^ 2 [MOD 2] := by
            have hprodEven : 2 ∣ S.card * (S.card + 1) := by
              rcases Nat.even_or_odd S.card with ⟨j, hj⟩ | ⟨j, hj⟩
              · exact ⟨j * (S.card + 1), by rw [hj]; ring⟩
              · exact ⟨S.card * (j + 1), by rw [hj]; ring⟩
            have hdiv : 2 * (S.card * (S.card + 1) / 2) = S.card * (S.card + 1) :=
              Nat.mul_div_cancel' hprodEven
            rw [Nat.ModEq]
            omega
          rw [neg_one_pow_eq_of_modEq (R := ℝ) hmod]

/-- The signed overlap coefficients from the Clifford blade swap law cancel
for all grades except the scalar and, in odd dimension, the top grade. -/
theorem shirokov_blade_swap_average_vanishes (n : ℕ)
    (T : Finset (Fin n))
    (hcase : (Even T.card ∧ T.Nonempty) ∨ (Odd T.card ∧
      T ≠ (Finset.univ : Finset (Fin n)))) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) = 0 := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact shirokov_blade_swap_sign_character n S T
    _ = 0 := shirokov_noncentral_blade_character_vanishes n T hcase

/-- The actual inverse-blade Reynolds sum annihilates every noncentral blade
in the standard `Cl(0,n)` basis. The scalar and odd-dimensional top grades
are excluded by `hcase` and require the corresponding fixed-point calculation. -/
theorem shirokov_noncentral_blade_reynolds_vanishes (n : ℕ)
    (T : Finset (Fin n))
    (hcase : (Even T.card ∧ T.Nonempty) ∨ (Odd T.card ∧
      T ≠ (Finset.univ : Finset (Fin n)))) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) = 0 := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n T * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact shirokov_inverse_blade_conjugation_sign n S T
    _ = (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
          rw [← Finset.sum_smul]
    _ = 0 := by
          have hcoef :
              (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) = 0 := by
            exact_mod_cast shirokov_blade_swap_average_vanishes n T hcase
          rw [hcoef]
          simp

/-- The standard inverse-blade Reynolds average fixes the scalar blade with
the expected orbit-count factor `2^n`. -/
theorem shirokov_scalar_blade_reynolds_average (n : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n ∅ * cBlade ℝ n S) =
      (2 ^ n : ℝ) • cBlade ℝ n ∅ := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n ∅ * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (1 : ℝ) • cBlade ℝ n ∅ := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [shirokov_inverse_blade_conjugation_sign]
          simp [cBlade_empty]
    _ = (2 ^ n : ℝ) • cBlade ℝ n ∅ := by
          rw [← Finset.sum_smul]
          simp

/-- Finite complement pairing reduces a complement-invariant powerset sum in
odd dimension to subsets whose size is strictly below the midpoint. This is
the combinatorial core of the odd-dimensional reduced sum in equation (2.3);
complement invariance is kept as an explicit hypothesis. -/
theorem shirokov_odd_complement_sum_reduction {A : Type*} [AddCommMonoid A]
    (n : ℕ) (hn : Odd n) (f : Finset (Fin n) → A)
    (hcomp : ∀ S : Finset (Fin n),
      f S = f ((Finset.univ : Finset (Fin n)) \ S)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, f S) =
      2 • ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
        (fun S => 2 * S.card < n), f S := by
  classical
  rcases hn with ⟨k, hk⟩
  let P := (Finset.univ : Finset (Fin n)).powerset
  let L := P.filter (fun S => 2 * S.card < n)
  let U := P.filter (fun S => n < 2 * S.card)
  have hcard (S : Finset (Fin n)) :
      ((Finset.univ : Finset (Fin n)) \ S).card = n - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fin]
  have hdouble (S : Finset (Fin n)) :
      2 * S.card < n ↔ n < 2 * ((Finset.univ : Finset (Fin n)) \ S).card := by
    rw [hcard]
    omega
  have hsum : (∑ S ∈ L, f S) = ∑ S ∈ U, f S := by
    refine Finset.sum_bij (fun S _ => (Finset.univ : Finset (Fin n)) \ S)
      ?_ ?_ ?_ ?_
    · intro S hS
      change S ∈ P.filter (fun T => 2 * T.card < n) at hS
      have hlow := (Finset.mem_filter.mp hS).2
      change (Finset.univ : Finset (Fin n)) \ S ∈
        P.filter (fun T => n < 2 * T.card)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, (hdouble S).mp hlow⟩
    · intro S hS T hT hST
      have h := congrArg (fun X : Finset (Fin n) =>
        (Finset.univ : Finset (Fin n)) \ X) hST
      have hdoubleComp :
          (Finset.univ : Finset (Fin n)) \ ((Finset.univ : Finset (Fin n)) \ T) = T := by
        ext i
        simp
      simpa [hdoubleComp] using h
    · intro T hT
      change T ∈ P.filter (fun S => n < 2 * S.card) at hT
      have hhigh := (Finset.mem_filter.mp hT).2
      refine ⟨(Finset.univ : Finset (Fin n)) \ T, ?_, ?_⟩
      · change (Finset.univ : Finset (Fin n)) \ T ∈
          P.filter (fun S => 2 * S.card < n)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,
            (hdouble ((Finset.univ : Finset (Fin n)) \ T)).mpr (by simpa using hhigh)⟩
      · ext i
        simp
    · intro S hS
      exact hcomp S
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro S hL hU
    have hlow := (Finset.mem_filter.mp hL).2
    have hhigh := (Finset.mem_filter.mp hU).2
    omega
  have hunion : L ∪ U = P := by
    ext S
    simp only [L, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hP, _⟩ | ⟨hP, _⟩) <;> exact hP
    · intro hP
      have hne : 2 * S.card ≠ n := by omega
      rcases lt_or_gt_of_ne hne with hlow | hhigh
      · exact Or.inl ⟨hP, hlow⟩
      · exact Or.inr ⟨hP, hhigh⟩
  calc
    (∑ S ∈ P, f S) = ∑ S ∈ L ∪ U, f S := by rw [hunion]
    _ = (∑ S ∈ L, f S) + ∑ S ∈ U, f S := Finset.sum_union hdisj
    _ = (∑ S ∈ L, f S) + ∑ S ∈ L, f S := by rw [← hsum]
    _ = 2 • ∑ S ∈ L, f S := by simp [two_nsmul]

/-- In odd dimension, conjugation sign characters for a blade and its
complement agree. This supplies complement invariance for each standard-frame
blade summand of the Reynolds operator. -/
theorem shirokov_odd_blade_character_complement_invariant (n : ℕ)
    (hn : Odd n) (S T : Finset (Fin n)) :
    (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2) =
      (-1 : ℝ) ^ ((Finset.univ \ S).card * T.card -
        ((Finset.univ : Finset (Fin n)) \ S ∩ T).card ^ 2) := by
  classical
  let g : Fin n → ℤ := fun i =>
    (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)
  have htotal : (∏ i : Fin n, g i) = 1 := by
    rcases hn with ⟨k, hk⟩
    have hkN : n = 2 * k + 1 := by omega
    have hchar := shirokov_blade_character_product n
      (Finset.univ : Finset (Fin n)) T
    have hcard : ((Finset.univ : Finset (Fin n)) ∩ T).card = T.card := by simp
    rw [hcard, Finset.card_univ, Fintype.card_fin] at hchar
    rw [hchar]
    have hexp : n * T.card + T.card = 2 * ((k + 1) * T.card) := by
      calc
        n * T.card + T.card = (2 * k + 1) * T.card + T.card :=
          congrArg (fun m : ℕ => m * T.card + T.card) hkN
        _ = 2 * ((k + 1) * T.card) := by ring
    rw [hexp, pow_mul]
    norm_num
  have hprodS : (∏ i ∈ S, g i) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i hi
    dsimp [g]
    rw [← pow_mul]
    norm_num
  have hsplit : (∏ i ∈ Finset.univ \ S, g i) * ∏ i ∈ S, g i = 1 := by
    rw [Finset.prod_sdiff (Finset.subset_univ S), htotal]
  have hprodEq : (∏ i ∈ Finset.univ \ S, g i) = ∏ i ∈ S, g i := by
    calc
      ∏ i ∈ Finset.univ \ S, g i =
          (∏ i ∈ Finset.univ \ S, g i) * (∏ i ∈ S, g i) ^ 2 := by
            rw [hprodS, mul_one]
      _ = ((∏ i ∈ Finset.univ \ S, g i) * ∏ i ∈ S, g i) *
          ∏ i ∈ S, g i := by ring
      _ = ∏ i ∈ S, g i := by rw [hsplit, one_mul]
  have hcharS := shirokov_blade_swap_sign_character n S T
  have hcharComp := shirokov_blade_swap_sign_character n (Finset.univ \ S) T
  have hsign : (-1 : ℤ) ^
      ((Finset.univ \ S).card * T.card - ((Finset.univ \ S) ∩ T).card ^ 2) =
      (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2) := by
    calc
      (-1 : ℤ) ^
          ((Finset.univ \ S).card * T.card - ((Finset.univ \ S) ∩ T).card ^ 2) =
        ∏ i ∈ Finset.univ \ S, g i := by simpa [g] using hcharComp
      _ = ∏ i ∈ S, g i := hprodEq
      _ = (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2) := by
        simpa [g] using hcharS.symm
  exact_mod_cast hsign.symm

/-- In odd dimension, the standard inverse-blade Reynolds sum of a basis blade
reduces to twice its lower-half subset sum. This is the fixed standard frame;
it does not yet transport equation (2.3) to a moving dual frame. -/
theorem shirokov_odd_blade_reynolds_reduced_sum (n : ℕ) (hn : Odd n)
    (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) =
      2 • ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
        (fun S => 2 * S.card < n),
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n T * cBlade ℝ n S := by
  let f : Finset (Fin n) → CliffordAlgebra (cliffordNegSqForm ℝ n) := fun S =>
    ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
      cBlade ℝ n T * cBlade ℝ n S
  have hcomp : ∀ S : Finset (Fin n),
      f S = f ((Finset.univ : Finset (Fin n)) \ S) := by
    intro S
    dsimp [f]
    rw [shirokov_inverse_blade_conjugation_sign,
      shirokov_inverse_blade_conjugation_sign,
      shirokov_odd_blade_character_complement_invariant n hn S T]
  simpa [f] using
    shirokov_odd_complement_sum_reduction n hn f hcomp

/-- In odd dimension, the standard inverse-blade Reynolds average fixes the
top-grade pseudoscalar as well as the scalar blade. -/
theorem shirokov_odd_pseudoscalar_reynolds_average (n : ℕ) (hn : Odd n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n (Finset.univ : Finset (Fin n)) * cBlade ℝ n S) =
      (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
  have hnCard : Odd (Finset.univ : Finset (Fin n)).card := by simpa using hn
  obtain ⟨k, hk⟩ := hnCard
  have hkN : n = 2 * k + 1 := by simpa using hk
  have hfactor (i : Fin n) :
      (-1 : ℝ) ^ ((Finset.univ : Finset (Fin n)).card +
        if i ∈ (Finset.univ : Finset (Fin n)) then 1 else 0) = 1 := by
    simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin]
    rw [hkN]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n (Finset.univ : Finset (Fin n)) * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (1 : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [shirokov_inverse_blade_conjugation_sign]
          have hsign : (-1 : ℝ) ^
              (S.card * (Finset.univ : Finset (Fin n)).card -
                (S ∩ (Finset.univ : Finset (Fin n))).card ^ 2) = 1 := by
            have hchar := shirokov_blade_swap_sign_character n S
              (Finset.univ : Finset (Fin n))
            have hreal : (-1 : ℝ) ^
                (S.card * (Finset.univ : Finset (Fin n)).card -
                  (S ∩ (Finset.univ : Finset (Fin n))).card ^ 2) =
                ∏ i ∈ S, (-1 : ℝ) ^
                  ((Finset.univ : Finset (Fin n)).card +
                    if i ∈ (Finset.univ : Finset (Fin n)) then 1 else 0) := by
              exact_mod_cast hchar
            rw [hreal]
            simp only [hfactor, Finset.prod_const_one]
          rw [hsign]
    _ = (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
          rw [← Finset.sum_smul]
          simp

/-- The standard inverse-blade Reynolds average on any blade: only the scalar
and (in odd dimension) the top-grade blade survive. -/
theorem shirokov_blade_reynolds_formula (n : ℕ) (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) =
      if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
      if Odd n ∧ T = Finset.univ then
        (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0 := by
  by_cases hEmpty : T = ∅
  · subst T
    simp only [if_pos rfl]
    exact shirokov_scalar_blade_reynolds_average n
  by_cases hTop : Odd n ∧ T = Finset.univ
  · rw [if_neg hEmpty, if_pos hTop]
    simpa [hTop.2] using shirokov_odd_pseudoscalar_reynolds_average n hTop.1
  rw [if_neg hEmpty, if_neg hTop]
  have hne : T.Nonempty := by
    by_contra h
    apply hEmpty
    exact Finset.not_nonempty_iff_eq_empty.mp h
  have hcase : (Even T.card ∧ T.Nonempty) ∨
      (Odd T.card ∧ T ≠ (Finset.univ : Finset (Fin n))) := by
    rcases Nat.even_or_odd T.card with hEven | hOdd
    · exact Or.inl ⟨hEven, hne⟩
    · exact Or.inr ⟨hOdd, fun h => hTop ⟨by simpa [h] using hOdd, h⟩⟩
  exact shirokov_noncentral_blade_reynolds_vanishes n T hcase

/-- The unnormalized standard-frame Reynolds operator on `Cl(0,n)`, written
using the explicit inverse-blade formula. -/
def shirokovReynolds (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
    ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
      cBlade ℝ n S

/-- Reynolds averaging acts coefficientwise on finite blade expansions. -/
theorem shirokov_reynolds_blade_expansion (n : ℕ)
    (a : Finset (Fin n) → ℝ) :
    shirokovReynolds n
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • cBlade ℝ n T) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • shirokovReynolds n (cBlade ℝ n T) := by
  simp only [shirokovReynolds, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          (a T • cBlade ℝ n T) * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • (((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n T * cBlade ℝ n S) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [mul_smul_comm, smul_mul_assoc]
    _ = a T • shirokovReynolds n (cBlade ℝ n T) := by
          rw [← Finset.smul_sum]
          rfl

/-- Explicit Reynolds action on an arbitrary finite linear combination of
ordered blades: the coefficient is retained only at scalar and odd top grade. -/
theorem shirokov_reynolds_finite_blade_support (n : ℕ)
    (a : Finset (Fin n) → ℝ) :
    shirokovReynolds n
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • cBlade ℝ n T) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
          if Odd n ∧ T = Finset.univ then
            (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0) := by
  rw [shirokov_reynolds_blade_expansion]
  apply Finset.sum_congr rfl
  intro T hT
  change a T • (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) = _
  rw [shirokov_blade_reynolds_formula]

/-- Coordinate readout of `Cl(0,n)` in the ordered blade family. -/
def shirokovBladeCoordinates (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) →ₗ[ℝ] Finset (Fin n) → ℝ where
  toFun := bladeRepr ℝ n
  map_add' x y := by simp [bladeRepr]
  map_smul' r x := by simp [bladeRepr]

@[simp]
theorem shirokovBladeCoordinates_cBlade (n : ℕ) (S : Finset (Fin n)) :
    shirokovBladeCoordinates n (cBlade ℝ n S) = Pi.single S 1 :=
  bladeRepr_cBlade ℝ n S

/-- The ordered blades span the full `Cl(0,n)` carrier: the coordinate readout
is onto, and the source and coordinate space have the same finite dimension. -/
theorem shirokov_blade_coordinates_injective (n : ℕ) :
    Function.Injective (shirokovBladeCoordinates n) := by
  let eBasis := (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra
  letI : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) :=
    eBasis.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
    (cliffordToExterior n).symm.finiteDimensional
  have hdim : Module.finrank ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      Module.finrank ℝ (Finset (Fin n) → ℝ) := by
    calc
      Module.finrank ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) =
          Module.finrank ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) :=
        LinearEquiv.finrank_eq (cliffordToExterior n)
      _ = Fintype.card (Finset (Fin n)) := Module.finrank_eq_card_basis eBasis
      _ = Module.finrank ℝ (Finset (Fin n) → ℝ) :=
        (Module.finrank_eq_card_basis (Pi.basisFun ℝ (Finset (Fin n)))).symm
  have hsurj : Function.Surjective (shirokovBladeCoordinates n) := by
    intro f
    refine ⟨∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      f S • cBlade ℝ n S, ?_⟩
    ext T
    simp [Pi.single_apply]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj

/-- The standard ordered blade family is linearly independent, as witnessed
by the owner's injective coordinate readout. -/
theorem shirokov_standard_blades_linearIndependent (n : ℕ) :
    LinearIndependent ℝ
      (fun S : Finset (Fin n) => cBlade ℝ n S) := by
  have hker : LinearMap.ker (shirokovBladeCoordinates n) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (shirokov_blade_coordinates_injective n)
  have hcoords : LinearIndependent ℝ
      (fun S : Finset (Fin n) =>
        shirokovBladeCoordinates n (cBlade ℝ n S)) := by
    simpa [Pi.basisFun] using
      (Pi.basisFun ℝ (Finset (Fin n))).linearIndependent
  exact (LinearMap.linearIndependent_iff
    (shirokovBladeCoordinates n) hker).mp hcoords

/-- Every element of `Cl(0,n)` has its canonical finite ordered-blade expansion. -/
theorem shirokov_blade_expansion (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    x = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      bladeRepr ℝ n x S • cBlade ℝ n S := by
  apply shirokov_blade_coordinates_injective n
  simp only [map_sum, map_smul, shirokovBladeCoordinates_cBlade]
  ext T
  change bladeRepr ℝ n x T = _
  simp [Pi.single_apply]

/-- On an arbitrary element, the polynomial in the frame-sandwich endomorphism
is the canonical grade-`k` projection in ordered-blade coordinates. -/
theorem shirokov_even_grade_projector_apply {n : ℕ} (hn : Even n)
    (k : Fin (n + 1)) (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovGradeProjector n k x =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if S.card = k.val then bladeRepr ℝ n x S • cBlade ℝ n S else 0 := by
  rw [shirokov_blade_expansion n x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro S hS
  have hrepr : bladeRepr ℝ n
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        bladeRepr ℝ n x T • cBlade ℝ n T) S = bladeRepr ℝ n x S :=
    congrArg (fun y => bladeRepr ℝ n y S) (shirokov_blade_expansion n x).symm
  have hgrade :
      ((⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩ :
        Fin (n + 1)) = k) ↔ S.card = k.val := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  rw [shirokov_even_grade_projector_blade hn k S]
  rw [← hrepr]
  simp [hgrade, smul_smul]

/-- Successive grade projectors select matching blade degree and annihilate
different degrees. -/
theorem shirokov_even_grade_projector_compose_blade {n : ℕ} (hn : Even n)
    (i k : Fin (n + 1)) (S : Finset (Fin n)) :
    shirokovGradeProjector n i (shirokovGradeProjector n k (cBlade ℝ n S)) =
      (if i = k ∧ S.card = k.val then (1 : ℝ) • cBlade ℝ n S else 0) := by
  let j : Fin (n + 1) :=
    ⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩
  have hjk : j = k ↔ S.card = k.val := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  rw [shirokov_even_grade_projector_blade hn k S]
  by_cases hS : S.card = k.val
  · have hj : j = k := hjk.mpr hS
    rw [if_pos hj, one_smul, shirokov_even_grade_projector_blade hn i S]
    by_cases hik : i = k
    · subst i
      simp [hS]
    · have hji : j ≠ i := by
        intro h
        apply hik
        exact h.symm.trans hj
      have hki : k ≠ i := by
        intro h
        exact hji (hj.trans h)
      simp [hik, hki, hS]
  · have hj : j ≠ k := fun h => hS (hjk.mp h)
    rw [if_neg hj, zero_smul, map_zero]
    simp [hS]

/-- The grade projectors are mutually orthogonal on arbitrary multivectors:
`P_i P_k = 0` for `i ≠ k`, and `P_k` is idempotent. -/
theorem shirokov_even_grade_projector_compose_apply {n : ℕ} (hn : Even n)
    (i k : Fin (n + 1)) (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovGradeProjector n i (shirokovGradeProjector n k x) =
      if i = k then shirokovGradeProjector n k x else 0 := by
  conv_lhs => arg 2; rw [shirokov_blade_expansion n x]
  simp only [map_sum, map_smul]
  rw [shirokov_even_grade_projector_apply hn k x]
  by_cases hik : i = k
  · subst i
    simp_rw [shirokov_even_grade_projector_compose_blade hn k k]
    simp
  · simp_rw [shirokov_even_grade_projector_compose_blade hn i k]
    simp [hik]

/-- Summing over all grades recovers the identity on the full Clifford
algebra, so the polynomial spectral projectors form a complete decomposition. -/
theorem shirokov_even_grade_projector_sum_apply {n : ℕ} (hn : Even n)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (∑ k : Fin (n + 1), shirokovGradeProjector n k x) = x := by
  calc
    (∑ k : Fin (n + 1), shirokovGradeProjector n k x) =
        ∑ k : Fin (n + 1), ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          if S.card = k.val then bladeRepr ℝ n x S • cBlade ℝ n S else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact shirokov_even_grade_projector_apply hn k x
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ k : Fin (n + 1),
          if S.card = k.val then bladeRepr ℝ n x S • cBlade ℝ n S else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        bladeRepr ℝ n x S • cBlade ℝ n S := by
      apply Finset.sum_congr rfl
      intro S hS
      let kS : Fin (n + 1) :=
        ⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩
      rw [Fintype.sum_eq_single kS (fun k hne => by
        have hkval : k.val ≠ S.card := by
          intro heq
          apply hne
          apply Fin.ext
          change k.val = S.card
          exact heq
        simp [Ne.symm hkval])]
      simp [kS]
    _ = x := (shirokov_blade_expansion n x).symm

/-- The subspace spanned by ordered blades of grade `k` in fixed `Cl(0,n)`. -/
def shirokovGradeSubspace (n : ℕ) (k : Fin (n + 1)) :
    Submodule ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
  Submodule.span ℝ {x | ∃ S : Finset (Fin n), S.card = k.val ∧ x = cBlade ℝ n S}

/-- The polynomial spectral projector has exactly the grade-`k` blade span as
its range. This identifies the abstract range with the paper's grade space. -/
theorem shirokov_even_grade_projector_range {n : ℕ} (hn : Even n)
    (k : Fin (n + 1)) :
    LinearMap.range (shirokovGradeProjector n k) = shirokovGradeSubspace n k := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    rw [shirokov_even_grade_projector_apply hn k y]
    apply sum_mem
    intro S hS
    by_cases hgrade : S.card = k.val
    · rw [if_pos hgrade]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨S, hgrade, rfl⟩)
    · rw [if_neg hgrade]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨S, hgrade, rfl⟩ := hx
    apply LinearMap.mem_range.mpr
    refine ⟨cBlade ℝ n S, ?_⟩
    rw [shirokov_even_grade_projector_blade hn k S]
    have hidx :
        (⟨S.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)⟩ :
          Fin (n + 1)) = k := by
      apply Fin.ext
      exact hgrade
    simp [hidx]

/-- Complementary inverse blades induce the same conjugation on every element
of the fixed finite-stage `Cl(0,n)` algebra when `n` is odd. -/
theorem shirokov_odd_inverse_blade_conjugation_complement (n : ℕ) (hn : Odd n)
    (S : Finset (Fin n)) (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
        cBlade ℝ n S) =
      (((-1 : ℝ) ^ ((Finset.univ \ S).card *
        ((Finset.univ \ S).card + 1) / 2) •
          cBlade ℝ n (Finset.univ \ S)) * x * cBlade ℝ n (Finset.univ \ S)) := by
  rw [shirokov_blade_expansion n x]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  have hblade :
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n T * cBlade ℝ n S =
        ((-1 : ℝ) ^ ((Finset.univ \ S).card *
          ((Finset.univ \ S).card + 1) / 2) •
            cBlade ℝ n (Finset.univ \ S)) * cBlade ℝ n T *
          cBlade ℝ n (Finset.univ \ S) := by
    rw [shirokov_inverse_blade_conjugation_sign,
      shirokov_inverse_blade_conjugation_sign,
      shirokov_odd_blade_character_complement_invariant n hn S T]
  simpa only [mul_smul_comm, smul_mul_assoc] using
    congrArg (fun y => bladeRepr ℝ n x T • y) hblade

/-- The standard inverse-blade Reynolds sum of any element of finite-stage
`Cl(0,n)` reduces to twice the lower-half sum in odd dimension. -/
theorem shirokov_odd_reynolds_reduced_sum (n : ℕ) (hn : Odd n)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
        cBlade ℝ n S) =
      2 • ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
        (fun S => 2 * S.card < n),
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
          cBlade ℝ n S := by
  apply shirokov_odd_complement_sum_reduction n hn
  intro S
  exact shirokov_odd_inverse_blade_conjugation_complement n hn S x

/-- Reynolds average on every element of the finite-stage Clifford algebra, in
ordered-blade coordinates. Its support is scalar, plus odd top grade. -/
theorem shirokov_reynolds_all_elements (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovReynolds n x =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        bladeRepr ℝ n x T • (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
          if Odd n ∧ T = Finset.univ then
            (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0) := by
  calc
    shirokovReynolds n x = shirokovReynolds n
        (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          bladeRepr ℝ n x T • cBlade ℝ n T) :=
            congrArg (shirokovReynolds n) (shirokov_blade_expansion n x)
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        bladeRepr ℝ n x T • (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
          if Odd n ∧ T = Finset.univ then
            (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0) :=
              shirokov_reynolds_finite_blade_support n (bladeRepr ℝ n x)

/-- Non-scalar, non-top blade coordinates of the Reynolds average vanish. This
is the support statement supplied by the finite-frame average; identifying
its range with the algebraic center still requires centrality of the odd top
blade. -/
theorem shirokov_reynolds_noncentral_coordinate_zero (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) (T : Finset (Fin n))
    (hEmpty : T ≠ ∅)
    (hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n)))) :
    bladeRepr ℝ n (shirokovReynolds n x) T = 0 := by
  change (shirokovBladeCoordinates n (shirokovReynolds n x)) T = 0
  rw [shirokov_reynolds_all_elements]
  simp only [map_sum, map_smul]
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro S hS
  have hcoord : (shirokovBladeCoordinates n
      (if S = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
        if Odd n ∧ S = (Finset.univ : Finset (Fin n)) then
          (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0)) T = 0 := by
    by_cases hSempty : S = ∅
    · subst S
      have hscalar : (shirokovBladeCoordinates n (cBlade ℝ n ∅)) T = 0 := by
        rw [shirokovBladeCoordinates_cBlade]
        simp [Pi.single_apply, hEmpty]
      have hscaled :
          (shirokovBladeCoordinates n ((2 ^ n : ℝ) • cBlade ℝ n ∅)) T = 0 := by
        rw [map_smul, Pi.smul_apply, hscalar]
        simp
      change (shirokovBladeCoordinates n ((2 ^ n : ℝ) • cBlade ℝ n ∅)) T = 0
      exact hscaled
    · by_cases hStop : Odd n ∧ S = (Finset.univ : Finset (Fin n))
      · rcases hStop with ⟨hn, hSall⟩
        subst S
        have htopcond : Odd n ∧ (Finset.univ : Finset (Fin n)) = Finset.univ :=
          ⟨hn, rfl⟩
        have hT : T ≠ (Finset.univ : Finset (Fin n)) := by
          intro hT
          exact hTop ⟨hn, hT⟩
        have htopcoord :
            (shirokovBladeCoordinates n (cBlade ℝ n (Finset.univ : Finset (Fin n)))) T = 0 := by
          simp [shirokovBladeCoordinates_cBlade, Pi.single_apply, hT]
        have hscaled :
            (shirokovBladeCoordinates n
              ((2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)))) T = 0 := by
          rw [map_smul, Pi.smul_apply, htopcoord]
          simp
        rw [if_neg hSempty, if_pos htopcond]
        exact hscaled
      · simp [hSempty, hStop]
  change bladeRepr ℝ n x S *
    (shirokovBladeCoordinates n
      (if S = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
        if Odd n ∧ S = (Finset.univ : Finset (Fin n)) then
          (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0)) T = 0
  rw [hcoord]
  simp

/-- In odd dimension, the top ordered blade commutes with every Clifford
generator, hence with the full algebra generated by those vectors. -/
theorem shirokov_odd_top_blade_mem_center (n : ℕ) (hn : Odd n) :
    cBlade ℝ n (Finset.univ : Finset (Fin n)) ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  have hsign : (-1 : ℝ) ^ (n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk]
    norm_num [pow_add, pow_mul]
  have hcommGen : ∀ r : Fin n,
      cGen ℝ n r * cBlade ℝ n (Finset.univ : Finset (Fin n)) =
        cBlade ℝ n (Finset.univ : Finset (Fin n)) * cGen ℝ n r := by
    intro r
    have h := cGen_mul_cBlade ℝ n r (Finset.univ : Finset (Fin n))
    simpa [Finset.card_fin, hsign] using h
  have hcommVec : ∀ v : Fin n → ℝ,
      cBlade ℝ n (Finset.univ : Finset (Fin n)) *
          CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v =
        CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v *
          cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
    intro v
    have hv : v = ∑ r : Fin n, v r • (Pi.single r (1 : ℝ)) := by
      ext i
      simp [Pi.single_apply]
    rw [hv]
    simp only [map_sum, map_smul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    change v r • (cBlade ℝ n Finset.univ * cGen ℝ n r) =
      v r • (cGen ℝ n r * cBlade ℝ n Finset.univ)
    rw [← hcommGen r]
  rw [Subalgebra.mem_center_iff]
  intro x
  have hx : x ∈ Algebra.adjoin ℝ
      (Set.range (CliffordAlgebra.ι (cliffordNegSqForm ℝ n))) := by
    rw [CliffordAlgebra.adjoin_range_ι (Q := cliffordNegSqForm ℝ n)]
    trivial
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro v hv
    rcases hv with ⟨v, rfl⟩
    exact (hcommVec v).symm
  · intro r
    exact Algebra.commutes r (cBlade ℝ n (Finset.univ : Finset (Fin n)))
  · intro a b ha hb hxa hxb
    rw [add_mul, mul_add, hxa, hxb]
  · intro a b ha hb hxa hxb
    calc
      (a * b) * cBlade ℝ n (Finset.univ : Finset (Fin n)) =
          a * (b * cBlade ℝ n (Finset.univ : Finset (Fin n))) := by rw [mul_assoc]
      _ = a * (cBlade ℝ n (Finset.univ : Finset (Fin n)) * b) := by rw [hxb]
      _ = (a * cBlade ℝ n (Finset.univ : Finset (Fin n))) * b := by rw [← mul_assoc]
      _ = (cBlade ℝ n (Finset.univ : Finset (Fin n)) * a) * b := by rw [hxa]
      _ = cBlade ℝ n (Finset.univ : Finset (Fin n)) * (a * b) := by rw [mul_assoc]

/-- The finite-frame Reynolds average is central: its coordinate support is
scalar, with the odd top blade central in odd dimension. -/
theorem shirokov_reynolds_mem_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovReynolds n x ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  let C := Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))
  rw [shirokov_reynolds_all_elements]
  apply Subalgebra.sum_mem
  intro T hT
  apply Subalgebra.smul_mem
  by_cases hEmpty : T = ∅
  · subst T
    simp only [if_pos rfl]
    rw [cBlade_empty]
    exact Subalgebra.smul_mem C (Subalgebra.one_mem C) (2 ^ n : ℝ)
  · by_cases hTop : Odd n ∧ T = (Finset.univ : Finset (Fin n))
    · rcases hTop with ⟨hn, rfl⟩
      rw [if_neg hEmpty, if_pos ⟨hn, rfl⟩]
      exact Subalgebra.smul_mem C (shirokov_odd_top_blade_mem_center n hn)
        (2 ^ n : ℝ)
    · simp [hEmpty, hTop]

/-- The unnormalized Reynolds average acts as multiplication by the number of
frame blades on every element of the algebraic center. -/
theorem shirokov_reynolds_eq_card_smul_of_mem_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))) :
    shirokovReynolds n x = (2 ^ n : ℝ) • x := by
  unfold shirokovReynolds
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
          cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, x := by
        apply Finset.sum_congr rfl
        intro S hS
        let b := cBlade ℝ n S
        let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
        have hcomm := (Subalgebra.mem_center_iff.mp hx) b
        have hinv := (shirokov_blade_inverse_formula n S).1
        change (ε • b) * x * b = x
        calc
          (ε • b) * x * b = ε • (b * x * b) := by simp only [smul_mul_assoc]
          _ = ε • (x * b * b) := by rw [hcomm]
          _ = x * ((ε • b) * b) := by noncomm_ring
          _ = x := by simpa [b, ε] using congrArg (fun z => x * z) hinv
    _ = (2 ^ n : ℝ) • x := by
      simp only [Finset.sum_const, Finset.card_powerset, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Algebra.smul_def]
      congr 1
      norm_cast

/-- The normalized standard-frame Reynolds operator, valued in the algebraic
center of the finite-stage Clifford algebra. -/
def shirokovCenterProjection (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  ((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x

/-- Explicit coordinate formula for the standard-frame projection onto the
center: it retains the scalar coordinate and, in odd dimension, the top one. -/
theorem shirokov_center_projection_coordinate_formula (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovCenterProjection n x = bladeRepr ℝ n x ∅ • cBlade ℝ n ∅ +
      if Odd n then
        bladeRepr ℝ n x (Finset.univ : Finset (Fin n)) •
          cBlade ℝ n (Finset.univ : Finset (Fin n))
      else 0 := by
  classical
  let ps := (Finset.univ : Finset (Fin n)).powerset
  have hpow : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcancel : ((2 ^ n : ℝ)⁻¹) * (2 ^ n : ℝ) = 1 := inv_mul_cancel₀ hpow
  have hscale (a : ℝ) (z : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
      ((2 ^ n : ℝ)⁻¹) • (a • ((2 ^ n : ℝ) • z)) = a • z := by
    rw [smul_smul, smul_smul]
    congr 1
    calc
      ((2 ^ n : ℝ)⁻¹) * a * (2 ^ n : ℝ) =
          a * (((2 ^ n : ℝ)⁻¹) * (2 ^ n : ℝ)) := by
            calc
              _ = (((2 ^ n : ℝ)⁻¹) * (2 ^ n : ℝ)) * a := by ac_rfl
              _ = _ := mul_comm _ _
      _ = a := by rw [hcancel, mul_one]
  by_cases hn : Odd n
  · have hnpos : 0 < n := hn.pos
    have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
      intro h
      have hmem := Finset.mem_univ (⟨0, hnpos⟩ : Fin n)
      rw [← h] at hmem
      simp at hmem
    rw [shirokovCenterProjection, shirokov_reynolds_all_elements]
    have hsplit :
        (∑ T ∈ ps, bladeRepr ℝ n x T •
          (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
            if Odd n ∧ T = Finset.univ then
              (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0)) =
          bladeRepr ℝ n x ∅ • ((2 ^ n : ℝ) • cBlade ℝ n ∅) +
            bladeRepr ℝ n x Finset.univ •
              ((2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n))) := by
      calc
        _ = (∑ T ∈ ps, if T = ∅ then
              bladeRepr ℝ n x T • ((2 ^ n : ℝ) • cBlade ℝ n ∅) else 0) +
            ∑ T ∈ ps, if T = Finset.univ then
              bladeRepr ℝ n x T • ((2 ^ n : ℝ) •
                cBlade ℝ n (Finset.univ : Finset (Fin n))) else 0 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro T hT
              by_cases he : T = ∅
              · subst T
                simp [hne]
              · by_cases ht : T = Finset.univ
                · subst T
                  simp [hn, ne_comm.mp hne]
                · simp [he, ht]
        _ = _ := by
              rw [Finset.sum_eq_single_of_mem ∅ (by simp [ps]),
                Finset.sum_eq_single_of_mem Finset.univ (by simp [ps])]
              · simp
              · intro T hT hneT
                simp [hneT]
              · intro T hT hneT
                simp [hneT]
    rw [hsplit]
    rw [if_pos hn]
    rw [smul_add, hscale, hscale]
  · rw [shirokovCenterProjection, shirokov_reynolds_all_elements]
    have hsum :
        (∑ T ∈ ps, bladeRepr ℝ n x T •
          (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
            if Odd n ∧ T = Finset.univ then
              (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0)) =
          bladeRepr ℝ n x ∅ • ((2 ^ n : ℝ) • cBlade ℝ n ∅) := by
      rw [Finset.sum_eq_single_of_mem ∅ (by simp [ps])]
      · simp [hn]
      · intro T hT hneT
        simp [hn, hneT]
    rw [hsum]
    rw [if_neg hn]
    rw [hscale]
    simp

theorem shirokovCenterProjection_mem_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovCenterProjection n x ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  apply Subalgebra.smul_mem _ (shirokov_reynolds_mem_center n x)

theorem shirokovCenterProjection_fixes_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))) :
    shirokovCenterProjection n x = x := by
  have hpow : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  change ((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x = x
  rw [shirokov_reynolds_eq_card_smul_of_mem_center n x hx, smul_smul]
  simp [hpow]

theorem shirokovCenterProjection_idempotent (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovCenterProjection n (shirokovCenterProjection n x) =
      shirokovCenterProjection n x :=
  shirokovCenterProjection_fixes_center n _
    (shirokovCenterProjection_mem_center n x)

/-- Central elements of the finite-stage `Cl(0,n)` have no blade coordinates
outside the scalar and odd-dimensional top grades. -/
theorem shirokov_center_coordinate_support (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (T : Finset (Fin n)) (hEmpty : T ≠ ∅)
    (hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n)))) :
    bladeRepr ℝ n x T = 0 := by
  have hfix := shirokovCenterProjection_fixes_center n x hx
  have hzero := shirokov_reynolds_noncentral_coordinate_zero n x T hEmpty hTop
  change (shirokovBladeCoordinates n (shirokovReynolds n x)) T = 0 at hzero
  change (shirokovBladeCoordinates n x) T = 0
  rw [← hfix]
  change (shirokovBladeCoordinates n
      (((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x)) T = 0
  rw [map_smul, Pi.smul_apply, hzero]
  simp

/-- A central element of the finite-stage `Cl(0,n)` is determined by its
scalar coordinate and, in odd dimension, its top-blade coordinate. -/
theorem shirokov_center_two_coordinate_expansion (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))) :
    x = bladeRepr ℝ n x ∅ • cBlade ℝ n ∅ +
      if Odd n then
        bladeRepr ℝ n x (Finset.univ : Finset (Fin n)) •
          cBlade ℝ n (Finset.univ : Finset (Fin n))
      else 0 := by
  classical
  apply shirokov_blade_coordinates_injective
  ext T
  simp only [map_add, map_smul, shirokovBladeCoordinates_cBlade,
    Pi.smul_apply, Pi.single_apply]
  change bladeRepr ℝ n x T = _
  have hsupport (hEmpty : T ≠ ∅)
      (hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n)))) :
      bladeRepr ℝ n x T = 0 :=
    shirokov_center_coordinate_support n x hx T hEmpty hTop
  by_cases hEmpty : T = ∅
  · subst T
    by_cases hOdd : Odd n
    · have hnpos : 0 < n := hOdd.pos
      have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
        intro h
        have hmem : (⟨0, hnpos⟩ : Fin n) ∈
            (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        rw [h] at hmem
        simpa using hmem
      simp [hOdd, hne]
    · simp [hOdd]
  · by_cases hOdd : Odd n
    · by_cases hTop : T = (Finset.univ : Finset (Fin n))
      · subst T
        have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
          intro h
          have hnpos : 0 < n := hOdd.pos
          have hmem : (⟨0, hnpos⟩ : Fin n) ∈
              (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
          rw [h] at hmem
          simpa using hmem
        simp [hOdd, hEmpty, hne]
      · have hcoord := hsupport hEmpty (by simp [hOdd, hTop])
        simp [hOdd, hEmpty, hTop, hcoord]
    · have hcoord := hsupport hEmpty (by simp [hOdd])
      simp [hOdd, hEmpty, hcoord]

/-- A central element of `Cl(0,n)` supported only in blade grade two is zero.
The scalar center coordinate and the odd-dimensional top coordinate cannot
occur in grade two. -/
theorem shirokov_center_grade_two_eq_zero (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n x T ≠ 0 → T.card = 2) :
    x = 0 := by
  apply shirokov_blade_coordinates_injective
  ext T
  rw [map_zero]
  change bladeRepr ℝ n x T = 0
  have hcoord : bladeRepr ℝ n x T = 0 := by
    by_contra hne
    have hcard := hgrade T hne
    have hEmpty : T ≠ ∅ := by
      intro h
      subst T
      simp at hcard
    have hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n))) := by
      rintro ⟨hn, rfl⟩
      have hcard' : n = 2 := by simpa using hcard
      subst n
      norm_num at hn
    exact hne (shirokov_center_coordinate_support n x hx T hEmpty hTop)
  exact hcoord

/-- Bracketing two adjacent ordered simple bivectors in the fixed negative
Clifford carrier produces the third bivector, with the sign determined by
the generator square `-1`. This is a basis-level instance of grade-two Lie
closure; it does not yet establish closure for arbitrary grade-two sums. -/
private theorem shirokov_cGen_pair_eq_blade {n : ℕ} {i k : Fin n} (hik : i < k) :
    cGen ℝ n i * cGen ℝ n k = cBlade ℝ n {i, k} := by
  have hne : i ≠ k := ne_of_lt hik
  have hlen : (bladeList ({i, k} : Finset (Fin n))).length = 2 := by
    rw [bladeList_length, Finset.card_pair hne]
  have hpw := bladeList_pairwise_lt ({i, k} : Finset (Fin n))
  have hlist : bladeList ({i, k} : Finset (Fin n)) = [i, k] := by
    rcases hL : bladeList ({i, k} : Finset (Fin n)) with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · simp [hL] at hlen
    · simp [hL] at hlen
    · rw [hL] at hpw
      have hab : a < b := (List.pairwise_cons.mp hpw).1 b (by simp)
      have ha : a ∈ ({i, k} : Finset (Fin n)) :=
        mem_bladeList.mp (by rw [hL]; simp)
      have hb : b ∈ ({i, k} : Finset (Fin n)) :=
        mem_bladeList.mp (by rw [hL]; simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (lt_irrefl _ hab)
      · rfl
      · exact False.elim (lt_irrefl _ (lt_trans hik hab))
      · exact False.elim (lt_irrefl _ hab)
    · simp [hL] at hlen
  simp [cBlade, hlist]

theorem shirokov_adjacent_simple_bivector_bracket {n : ℕ}
    {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    algebraCommutator (cGen ℝ n i * cGen ℝ n j)
        (cGen ℝ n j * cGen ℝ n k) =
      (-2 : ℝ) • cBlade ℝ n {i, k} := by
  have hii : cGen ℝ n j * cGen ℝ n j =
      -(1 : CliffordAlgebra (cliffordNegSqForm ℝ n)) := cGen_sq ℝ n j
  have hji : cGen ℝ n j * cGen ℝ n i = -(cGen ℝ n i * cGen ℝ n j) :=
    cGen_anticomm hij.ne'
  have hkj : cGen ℝ n k * cGen ℝ n j = -(cGen ℝ n j * cGen ℝ n k) :=
    cGen_anticomm hjk.ne'
  have hki : cGen ℝ n k * cGen ℝ n i = -(cGen ℝ n i * cGen ℝ n k) :=
    cGen_anticomm (lt_trans hij hjk).ne'
  have hleft :
      (cGen ℝ n i * cGen ℝ n j) * (cGen ℝ n j * cGen ℝ n k) =
        -(cGen ℝ n i * cGen ℝ n k) := by
    rw [show (cGen ℝ n i * cGen ℝ n j) * (cGen ℝ n j * cGen ℝ n k) =
      cGen ℝ n i * (cGen ℝ n j * cGen ℝ n j) * cGen ℝ n k by noncomm_ring,
      hii]
    noncomm_ring
  have hright :
      (cGen ℝ n j * cGen ℝ n k) * (cGen ℝ n i * cGen ℝ n j) =
        cGen ℝ n i * cGen ℝ n k := by
    calc
      (cGen ℝ n j * cGen ℝ n k) * (cGen ℝ n i * cGen ℝ n j) =
          cGen ℝ n j * (cGen ℝ n k * cGen ℝ n i) * cGen ℝ n j := by
            noncomm_ring
      _ = cGen ℝ n j * (-(cGen ℝ n i * cGen ℝ n k)) * cGen ℝ n j := by
            rw [hki]
      _ = -((cGen ℝ n j * cGen ℝ n i) *
          (cGen ℝ n k * cGen ℝ n j)) := by noncomm_ring
      _ = -((-(cGen ℝ n i * cGen ℝ n j)) *
          (-(cGen ℝ n j * cGen ℝ n k))) := by rw [hji, hkj]
      _ = -((cGen ℝ n i * cGen ℝ n j) *
          (cGen ℝ n j * cGen ℝ n k)) := by noncomm_ring
      _ = cGen ℝ n i * cGen ℝ n k := by rw [hleft]; simp
  rw [algebraCommutator, hleft, hright]
  rw [shirokov_cGen_pair_eq_blade (lt_trans hij hjk)]
  module

/-- The adjacent-generator bracket has blade-coordinate support in grade two. -/
theorem shirokov_adjacent_simple_bivector_bracket_grade_two
    {n : ℕ} {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (T : Finset (Fin n))
    (hT : bladeRepr ℝ n
      (algebraCommutator (cGen ℝ n i * cGen ℝ n j)
        (cGen ℝ n j * cGen ℝ n k)) T ≠ 0) :
    T.card = 2 := by
  have hcoord : bladeRepr ℝ n
      (algebraCommutator (cGen ℝ n i * cGen ℝ n j)
        (cGen ℝ n j * cGen ℝ n k)) T =
      if T = {i, k} then -2 else 0 := by
    rw [shirokov_adjacent_simple_bivector_bracket hij hjk]
    change ((cliffordEndRep ℝ n) ((-2 : ℝ) • cBlade ℝ n {i, k})
      (Pi.single ∅ (1 : ℝ))) T = if T = {i, k} then -2 else 0
    have hrepr :
        (cliffordEndRep ℝ n (cBlade ℝ n {i, k})) (Pi.single ∅ (1 : ℝ)) =
          Pi.single ({i, k} : Finset (Fin n)) (1 : ℝ) := by
      simpa [bladeRepr] using bladeRepr_cBlade ℝ n ({i, k} : Finset (Fin n))
    rw [map_smul]
    simp only [LinearMap.smul_apply, Pi.smul_apply]
    rw [hrepr]
    simp only [Pi.single_apply]
    split_ifs <;> simp [Finset.card_pair (ne_of_lt (lt_trans hij hjk))]
  rw [hcoord] at hT
  by_cases hEq : T = {i, k}
  · rw [hEq, Finset.card_pair (ne_of_lt (lt_trans hij hjk))]
  · simp [hEq] at hT

/-- The commutator of any two ordered grade-two blades is supported in grade
two in the fixed negative Clifford carrier. Even overlaps commute; a
one-generator overlap produces the symmetric-difference blade. -/
theorem shirokov_grade_two_blade_commutator_support {n : ℕ}
    (S T U : Finset (Fin n)) (hS : S.card = 2) (hT : T.card = 2)
    (hcoord : bladeRepr ℝ n
      (algebraCommutator (cBlade ℝ n S) (cBlade ℝ n T)) U ≠ 0) :
    U.card = 2 := by
  let k := (S ∩ T).card
  have hk_le : k ≤ 2 := by
    dsimp [k]
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
  have hswap := (cBlade_mul_swap_overlap ℝ n S T).2
  have hzero : cBlade ℝ n S * cBlade ℝ n T =
      cBlade ℝ n T * cBlade ℝ n S →
      bladeRepr ℝ n (algebraCommutator (cBlade ℝ n S) (cBlade ℝ n T)) U = 0 := by
    intro h
    rw [algebraCommutator, h]
    simp [bladeRepr]
  by_cases hk0 : k = 0
  · have hcomm : cBlade ℝ n S * cBlade ℝ n T =
        cBlade ℝ n T * cBlade ℝ n S := by
      have hsimp := hswap
      simp [k, hS, hT, hk0] at hsimp
      have hp : (-1 : ℝ) ^ 4 = 1 := by norm_num
      rw [hp, one_smul] at hsimp
      exact hsimp
    exact False.elim (hcoord (hzero hcomm))
  · by_cases hk1 : k = 1
    · obtain ⟨s, hs⟩ := InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas.cBlade_mul_cBlade_eq_signed_symmDiff ℝ n S T
      have hanti : cBlade ℝ n S * cBlade ℝ n T =
          -(cBlade ℝ n T * cBlade ℝ n S) := by
        have hsimp := hswap
        simp [k, hS, hT, hk1] at hsimp
        have hp : (-1 : ℝ) ^ 3 = -1 := by norm_num
        rw [hp, neg_one_smul] at hsimp
        exact hsimp
      have hsymm_card : (symmDiff S T).card = 2 := by
        rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
        · have hleft : (S \ T).card = 1 := by
            have hcard := Finset.card_sdiff_add_card_inter S T
            dsimp [k] at hk1
            omega
          have hright : (T \ S).card = 1 := by
            have hcard := Finset.card_sdiff_add_card_inter T S
            have hinter : (T ∩ S).card = 1 := by
              simpa [Finset.inter_comm] using hk1
            omega
          simp [hleft, hright]
        · refine Finset.disjoint_left.mpr ?_
          intro x hxST hxTS
          exact (Finset.mem_sdiff.mp hxTS).2 (Finset.mem_sdiff.mp hxST).1
      have hcomm : algebraCommutator (cBlade ℝ n S) (cBlade ℝ n T) =
          (2 * ((s : ℤ) : ℝ)) • cBlade ℝ n (symmDiff S T) := by
        have hrev : cBlade ℝ n T * cBlade ℝ n S =
            -(cBlade ℝ n S * cBlade ℝ n T) := by rw [hanti]; simp
        have hcomm' : algebraCommutator (cBlade ℝ n S) (cBlade ℝ n T) =
            2 • (cBlade ℝ n S * cBlade ℝ n T) := by
          rw [algebraCommutator, hrev]
          module
        rw [hcomm', hs]
        module
      have hU : U = symmDiff S T := by
        by_contra hU
        apply hcoord
        rw [hcomm]
        have hlinear : bladeRepr ℝ n
            ((2 * ((s : ℤ) : ℝ)) • cBlade ℝ n (symmDiff S T)) =
            (2 * ((s : ℤ) : ℝ)) • bladeRepr ℝ n (cBlade ℝ n (symmDiff S T)) := by
          simp [bladeRepr]
        rw [hlinear, bladeRepr_cBlade]
        simp [Pi.single_apply, hU]
      rw [hU]
      exact hsymm_card
    · have hk2 : k = 2 := by omega
      have hcomm : cBlade ℝ n S * cBlade ℝ n T =
          cBlade ℝ n T * cBlade ℝ n S := by
        have hsimp := hswap
        simp [k, hS, hT, hk2] at hsimp
        exact hsimp
      exact False.elim (hcoord (hzero hcomm))

/-- The coordinate-defined grade-two subspace of the fixed `Cl(0,n)` carrier. -/
def shirokovGradeTwoSpan (n : ℕ) :
    Submodule ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
  Submodule.span ℝ (Set.range fun S : {S : Finset (Fin n) // S.card = 2} =>
    cBlade ℝ n S.1)

/-- An element with only grade-two ordered-blade coordinates belongs to the
span of the grade-two blades. -/
theorem shirokov_grade_two_supported_mem_span (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hgrade : ∀ S : Finset (Fin n), bladeRepr ℝ n x S ≠ 0 → S.card = 2) :
    x ∈ shirokovGradeTwoSpan n := by
  rw [shirokov_blade_expansion n x]
  apply Submodule.sum_mem
  intro S hS
  by_cases hcoord : bladeRepr ℝ n x S = 0
  · simp [hcoord]
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range.mpr ⟨⟨S, hgrade S hcoord⟩, rfl⟩

/-- Coordinates outside grade two vanish on the grade-two blade submodule. -/
theorem shirokov_grade_two_span_coordinate_eq_zero (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ shirokovGradeTwoSpan n) (U : Finset (Fin n))
    (hU : U.card ≠ 2) : bladeRepr ℝ n x U = 0 := by
  have hcoord_span : ∀ z ∈ shirokovGradeTwoSpan n,
      shirokovBladeCoordinates n z U = 0 := by
    intro z hz
    change z ∈ Submodule.span ℝ
      (Set.range fun S : {S : Finset (Fin n) // S.card = 2} => cBlade ℝ n S.1) at hz
    refine Submodule.span_induction (R := ℝ)
      (p := fun z _ => shirokovBladeCoordinates n z U = 0) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨S, rfl⟩
      have hUS : U ≠ S.1 := by
        intro heq
        apply hU
        simpa [heq] using S.2
      simp [shirokovBladeCoordinates_cBlade, Pi.single_apply, hUS]
    · simp [shirokovBladeCoordinates]
    · intro z w _ _ hz hw
      simp only [map_add, Pi.add_apply]
      rw [hz, hw, zero_add]
    · intro r z _ hz
      simp only [map_smul, Pi.smul_apply]
      rw [hz, smul_zero]
  have hzero := hcoord_span x hx
  exact hzero

private theorem algebraCommutator_add_left {A : Type*} [Ring A]
    (x y z : A) : algebraCommutator (x + y) z =
      algebraCommutator x z + algebraCommutator y z := by
  simp only [algebraCommutator, add_mul, mul_add]
  noncomm_ring

private theorem algebraCommutator_add_right {A : Type*} [Ring A]
    (x y z : A) : algebraCommutator x (y + z) =
      algebraCommutator x y + algebraCommutator x z := by
  simp only [algebraCommutator, add_mul, mul_add]
  noncomm_ring

private theorem algebraCommutator_smul_left
    (r : ℝ) (x y : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    algebraCommutator (r • x) y = r • algebraCommutator x y := by
  simp only [algebraCommutator, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_sub]

private theorem algebraCommutator_smul_right
    (r : ℝ) (x y : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    algebraCommutator x (r • y) = r • algebraCommutator x y := by
  simp only [algebraCommutator, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_sub]

/-- Commutators of arbitrary elements supported in grade two remain in the
grade-two span. This lifts the ordered-blade pair calculation by bilinearity. -/
theorem shirokov_grade_two_commutator_mem_span (n : ℕ)
    (x y : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ shirokovGradeTwoSpan n) (hy : y ∈ shirokovGradeTwoSpan n) :
    algebraCommutator x y ∈ shirokovGradeTwoSpan n := by
  refine Submodule.span_induction
    (p := fun x _ => ∀ y ∈ shirokovGradeTwoSpan n,
      algebraCommutator x y ∈ shirokovGradeTwoSpan n)
    ?_ ?_ ?_ ?_ hx y hy
  · rintro z ⟨S, rfl⟩ y hy
    refine Submodule.span_induction
      (p := fun y _ => algebraCommutator (cBlade ℝ n S.1) y ∈
        shirokovGradeTwoSpan n) ?_ ?_ ?_ ?_ hy
    · rintro w ⟨T, rfl⟩
      apply shirokov_grade_two_supported_mem_span n
      intro U hU
      exact shirokov_grade_two_blade_commutator_support S.1 T.1 U S.2 T.2 hU
    · simp [algebraCommutator]
    · intro a b _ _ ha hb
      rw [algebraCommutator_add_right]
      exact (shirokovGradeTwoSpan n).add_mem ha hb
    · intro r a _ ha
      rw [algebraCommutator_smul_right]
      exact (shirokovGradeTwoSpan n).smul_mem r ha
  · simp [algebraCommutator]
  · intro x₁ x₂ _ _ hx₁ hx₂ z hz
    rw [algebraCommutator_add_left]
    exact (shirokovGradeTwoSpan n).add_mem (hx₁ z hz) (hx₂ z hz)
  · intro r x _ hx z hz
    rw [algebraCommutator_smul_left]
    exact (shirokovGradeTwoSpan n).smul_mem r (hx z hz)

/-- The coordinate support formulation of Lie closure for arbitrary
grade-two elements of the fixed negative Clifford carrier. -/
theorem shirokov_grade_two_commutator_closed (n : ℕ)
    (x y : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : ∀ S : Finset (Fin n), bladeRepr ℝ n x S ≠ 0 → S.card = 2)
    (hy : ∀ S : Finset (Fin n), bladeRepr ℝ n y S ≠ 0 → S.card = 2)
    (U : Finset (Fin n))
    (hcoord : bladeRepr ℝ n (algebraCommutator x y) U ≠ 0) :
    U.card = 2 := by
  have hspan := shirokov_grade_two_commutator_mem_span n x y
    (shirokov_grade_two_supported_mem_span n x hx)
    (shirokov_grade_two_supported_mem_span n y hy)
  by_contra hU
  exact hcoord (shirokov_grade_two_span_coordinate_eq_zero n
    (algebraCommutator x y) hspan U (by simpa using hU))

/-- Conditional flatness consequence for Shirokov's compatibility equation
in the negative-definite finite-stage Clifford algebra. Generator compatibility
and commuting derivation directions centralize the curvature defect; the
explicit grade-two support hypothesis then forces that central defect to zero.
This isolates the remaining geometric obligation: deriving `hgrade` from the
paper's frame hypotheses. -/
theorem shirokov_clifford_compatibility_curvature_eq_zero_of_grade_two
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgrade : ∀ T : Finset (Fin n),
      bladeRepr ℝ n
        (K.operatorAction x (C y) - K.operatorAction y (C x) -
          algebraCommutator (C x) (C y)) T ≠ 0 → T.card = 2) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  apply shirokov_center_grade_two_eq_zero n
    (K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y))
  · apply Subalgebra.mem_center_iff.mpr
    intro a
    have hcentral := shirokov_clifford_compatibility_curvature_central
      (Q := cliffordNegSqForm ℝ n) (K := K) (C := C) x y hxy hgen₁ hgen₂ a
    change
      (K.operatorAction x (C y) - K.operatorAction y (C x) -
        algebraCommutator (C x) (C y)) * a -
        a * (K.operatorAction x (C y) - K.operatorAction y (C x) -
          algebraCommutator (C x) (C y)) = 0 at hcentral
    exact (sub_eq_zero.mp hcentral).symm
  · exact hgrade

/-- If the connection values have a grade-two commutator, compatibility and
commuting directions force the curvature defect to vanish on `Cl(0,n)`. This
reduces the remaining geometric grade argument to bivector commutator closure. -/
theorem shirokov_curvature_flat_of_grade_two_connection_commutator
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hCx : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (C x) T ≠ 0 → T.card = 2)
    (hCy : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (C y) T ≠ 0 → T.card = 2) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  have hbracket : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (algebraCommutator (C x) (C y)) T ≠ 0 → T.card = 2 :=
    shirokov_grade_two_commutator_closed n (C x) (C y) hCx hCy
  have hcentral := shirokov_clifford_compatibility_curvature_central
    (Q := cliffordNegSqForm ℝ n) (K := K) (C := C) x y hxy hgen₁ hgen₂
  have hdef := shirokov_curvature_defect_eq_connection_commutator
    K C x y hgen₁ hgen₂
  have hcenter : algebraCommutator (C x) (C y) ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
    rw [Subalgebra.mem_center_iff]
    intro a
    have h := hcentral a
    change algebraCommutator
      (K.operatorAction x (C y) - K.operatorAction y (C x) -
        algebraCommutator (C x) (C y)) a = 0 at h
    rw [hdef] at h
    exact (sub_eq_zero.mp h).symm
  have hzero := shirokov_center_grade_two_eq_zero n
    (algebraCommutator (C x) (C y)) hcenter hbracket
  rw [hdef]
  exact hzero

/-- Subtraction preserves ordered-blade grade-two support. This packages the
linear-coordinate step needed to obtain support of a curvature expression
from support of its individual terms. -/
theorem shirokov_grade_two_support_sub (n : ℕ)
    (a b : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (ha : ∀ T : Finset (Fin n), bladeRepr ℝ n a T ≠ 0 → T.card = 2)
    (hb : ∀ T : Finset (Fin n), bladeRepr ℝ n b T ≠ 0 → T.card = 2) :
    ∀ T : Finset (Fin n), bladeRepr ℝ n (a - b) T ≠ 0 → T.card = 2 := by
  intro T hT
  by_contra hcard
  have haT : bladeRepr ℝ n a T = 0 := by
    by_contra hne
    exact hcard (ha T hne)
  have hbT : bladeRepr ℝ n b T = 0 := by
    by_contra hne
    exact hcard (hb T hne)
  have hcoord : bladeRepr ℝ n (a - b) T =
      bladeRepr ℝ n a T - bladeRepr ℝ n b T := by
    simp [bladeRepr]
  exact hT (by rw [hcoord, haT, hbT]; simp)

/-- A grade-two-preserving derivation direction sends grade-two connection
values to grade-two terms. With this preservation law in both directions,
grade-two connection coefficients, and generator compatibility, the curvature
defect vanishes. The preservation law remains an explicit geometric input. -/
theorem shirokov_clifford_compatibility_curvature_eq_zero_of_component_grade_two
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hCx : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (C x) T ≠ 0 → T.card = 2)
    (hCy : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (C y) T ≠ 0 → T.card = 2)
    (hKx : ∀ z ∈ shirokovGradeTwoSpan n,
      K.operatorAction x z ∈ shirokovGradeTwoSpan n)
    (hKy : ∀ z ∈ shirokovGradeTwoSpan n,
      K.operatorAction y z ∈ shirokovGradeTwoSpan n) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  have h₁ : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (K.operatorAction x (C y)) T ≠ 0 → T.card = 2 := by
    intro T hT
    by_contra hT2
    exact hT (shirokov_grade_two_span_coordinate_eq_zero n
      (K.operatorAction x (C y)) (hKx _
        (shirokov_grade_two_supported_mem_span n (C y) hCy)) T (by simpa using hT2))
  have h₂ : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (K.operatorAction y (C x)) T ≠ 0 → T.card = 2 := by
    intro T hT
    by_contra hT2
    exact hT (shirokov_grade_two_span_coordinate_eq_zero n
      (K.operatorAction y (C x)) (hKy _
        (shirokov_grade_two_supported_mem_span n (C x) hCx)) T (by simpa using hT2))
  apply shirokov_clifford_compatibility_curvature_eq_zero_of_grade_two
    n K C x y hxy hgen₁ hgen₂
  have hbracket : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (algebraCommutator (C x) (C y)) T ≠ 0 → T.card = 2 :=
    shirokov_grade_two_commutator_closed n (C x) (C y) hCx hCy
  have hsplit : K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = K.operatorAction x (C y) -
        (K.operatorAction y (C x) + algebraCommutator (C x) (C y)) := by
    noncomm_ring
  rw [hsplit]
  apply shirokov_grade_two_support_sub n
    (K.operatorAction x (C y))
    (K.operatorAction y (C x) + algebraCommutator (C x) (C y)) h₁
  intro T hT
  by_contra hcard
  have h₂T : bladeRepr ℝ n (K.operatorAction y (C x)) T = 0 := by
    by_contra hne
    exact hcard (h₂ T hne)
  have hbrT : bladeRepr ℝ n (algebraCommutator (C x) (C y)) T = 0 := by
    by_contra hne
    exact hcard (hbracket T hne)
  have hcoord : bladeRepr ℝ n
      (K.operatorAction y (C x) + algebraCommutator (C x) (C y)) T =
        bladeRepr ℝ n (K.operatorAction y (C x)) T +
          bladeRepr ℝ n (algebraCommutator (C x) (C y)) T := by
    simp [bladeRepr]
  exact hT (by rw [hcoord, h₂T, hbrT]; simp)

/-- Spin-type inner derivation actions preserve grade-two connection values.
The extra hypothesis identifies each direction's action with commutation by
a grade-two Clifford element. Preservation is derived from the owner's
grade-two commutator closure, rather than assumed as a submodule invariant.
This is still a finite-stage `Cl(0,n)` result; identifying the paper's
spacetime derivatives with these inner actions is a separate bridge. -/
theorem shirokov_clifford_compatibility_curvature_eq_zero_of_grade_two_inner_action
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (A : K.L → CliffordAlgebra (cliffordNegSqForm ℝ n))
    (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hCx : ∀ T : Finset (Fin n), bladeRepr ℝ n (C x) T ≠ 0 → T.card = 2)
    (hCy : ∀ T : Finset (Fin n), bladeRepr ℝ n (C y) T ≠ 0 → T.card = 2)
    (hAx : ∀ T : Finset (Fin n), bladeRepr ℝ n (A x) T ≠ 0 → T.card = 2)
    (hAy : ∀ T : Finset (Fin n), bladeRepr ℝ n (A y) T ≠ 0 → T.card = 2)
    (hInnerX : ∀ z, K.operatorAction x z = algebraCommutator (A x) z)
    (hInnerY : ∀ z, K.operatorAction y z = algebraCommutator (A y) z) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  apply shirokov_clifford_compatibility_curvature_eq_zero_of_component_grade_two
    n K C x y hxy hgen₁ hgen₂ hCx hCy
  · intro z hz
    have hzgrade : ∀ S : Finset (Fin n),
        bladeRepr ℝ n z S ≠ 0 → S.card = 2 := by
      intro S hS
      by_contra hS2
      exact hS (shirokov_grade_two_span_coordinate_eq_zero n z hz S
        (by simpa using hS2))
    have hcomm := shirokov_grade_two_commutator_mem_span n (A x) z
      (shirokov_grade_two_supported_mem_span n (A x) hAx)
      (shirokov_grade_two_supported_mem_span n z hzgrade)
    have hcommGrade : ∀ T : Finset (Fin n),
        bladeRepr ℝ n (algebraCommutator (A x) z) T ≠ 0 → T.card = 2 := by
      intro T hT
      by_contra hT2
      exact hT (shirokov_grade_two_span_coordinate_eq_zero n
        (algebraCommutator (A x) z) hcomm T (by simpa using hT2))
    rw [hInnerX z]
    exact shirokov_grade_two_supported_mem_span n
      (algebraCommutator (A x) z) hcommGrade
  · intro z hz
    have hzgrade : ∀ S : Finset (Fin n),
        bladeRepr ℝ n z S ≠ 0 → S.card = 2 := by
      intro S hS
      by_contra hS2
      exact hS (shirokov_grade_two_span_coordinate_eq_zero n z hz S
        (by simpa using hS2))
    have hcomm := shirokov_grade_two_commutator_mem_span n (A y) z
      (shirokov_grade_two_supported_mem_span n (A y) hAy)
      (shirokov_grade_two_supported_mem_span n z hzgrade)
    have hcommGrade : ∀ T : Finset (Fin n),
        bladeRepr ℝ n (algebraCommutator (A y) z) T ≠ 0 → T.card = 2 := by
      intro T hT
      by_contra hT2
      exact hT (shirokov_grade_two_span_coordinate_eq_zero n
        (algebraCommutator (A y) z) hcomm T (by simpa using hT2))
    rw [hInnerY z]
    exact shirokov_grade_two_supported_mem_span n
      (algebraCommutator (A y) z) hcommGrade

/-- A grade-two Clifford coefficient is uniquely determined by its commutator
action on all Clifford vectors. The difference centralizes the generators,
hence the generated algebra, and the center/grade-two intersection is zero.
This is the uniqueness component of Shirokov's spin-valued commutator system
on the fixed negative-definite finite-stage carrier. -/
theorem shirokov_grade_two_unique_of_vector_commutators (n : ℕ)
    (A B : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hA : ∀ T : Finset (Fin n), bladeRepr ℝ n A T ≠ 0 → T.card = 2)
    (hB : ∀ T : Finset (Fin n), bladeRepr ℝ n B T ≠ 0 → T.card = 2)
    (hcomm : ∀ v : Fin n → ℝ,
      algebraCommutator A (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) =
        algebraCommutator B (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v)) :
    A = B := by
  have hcentralVec : ∀ v : Fin n → ℝ,
      (A - B) * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v =
        CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * (A - B) := by
    intro v
    have h := hcomm v
    dsimp [algebraCommutator] at h
    calc
      (A - B) * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v =
          A * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
            B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v := by rw [sub_mul]
      _ = CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
          CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B := by
            calc
              _ = (A * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                  CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A) -
                    (B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) +
                    (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) := by abel
              _ = (B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                  CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) -
                    (B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) +
                    (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) := by rw [h]
              _ = CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
                    CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B := by abel
      _ = CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * (A - B) := by rw [mul_sub]
  have hcenter : A - B ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
    rw [Subalgebra.mem_center_iff]
    intro z
    have hz : z ∈ Algebra.adjoin ℝ
        (Set.range (CliffordAlgebra.ι (cliffordNegSqForm ℝ n))) := by
      rw [CliffordAlgebra.adjoin_range_ι (Q := cliffordNegSqForm ℝ n)]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
    · intro v hv
      rcases hv with ⟨v, rfl⟩
      exact (hcentralVec v).symm
    · intro r
      exact Algebra.commutes r (A - B)
    · intro x y hx hy hxc hyc
      rw [add_mul, mul_add, hxc, hyc]
    · intro x y hx hy hxc hyc
      calc
        (x * y) * (A - B) = x * (y * (A - B)) := by rw [mul_assoc]
        _ = x * ((A - B) * y) := by rw [hyc]
        _ = (x * (A - B)) * y := by rw [← mul_assoc]
        _ = ((A - B) * x) * y := by rw [hxc]
        _ = (A - B) * (x * y) := by rw [mul_assoc]
  have hgrade := shirokov_grade_two_support_sub n A B hA hB
  have hzero := shirokov_center_grade_two_eq_zero n (A - B) hcenter hgrade
  exact sub_eq_zero.mp hzero

/-- The standard-frame center projection annihilates elements supported only
in grade two, because the Reynolds average retains only scalar and odd-top
coordinates. -/
theorem shirokov_center_projection_eq_zero_of_grade_two (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n x T ≠ 0 → T.card = 2) :
    shirokovCenterProjection n x = 0 := by
  have hReynolds : shirokovReynolds n x = 0 := by
    rw [shirokov_reynolds_all_elements]
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hzero : bladeRepr ℝ n x T = 0
    · simp [hzero]
    · have hcard := hgrade T hzero
      have hEmpty : T ≠ ∅ := by
        intro h
        subst T
        simp at hcard
      have hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n))) := by
        rintro ⟨hn, rfl⟩
        have hcard' : n = 2 := by simpa using hcard
        subst n
        norm_num at hn
      simp [hEmpty, hTop]
  simp [shirokovCenterProjection, hReynolds]

/-- Each inverse ordered blade is a unit; this is the standard finite frame
used by the Reynolds average. -/
noncomputable def shirokovInverseBladeUnit (n : ℕ) (S : Finset (Fin n)) :
    (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ :=
  Units.mk
    (((-1 : ℝ) ^ (S.card * (S.card + 1) / 2)) • cBlade ℝ n S)
    (cBlade ℝ n S)
    (shirokov_blade_inverse_formula n S).1
    (shirokov_blade_inverse_formula n S).2

@[simp] theorem shirokovInverseBladeUnit_val (n : ℕ) (S : Finset (Fin n)) :
    (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2)) • cBlade ℝ n S := rfl

@[simp] theorem shirokovInverseBladeUnit_inv_val (n : ℕ) (S : Finset (Fin n)) :
    (((shirokovInverseBladeUnit n S)⁻¹ :
      (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) = cBlade ℝ n S := rfl

/-- The unit-conjugation average over the standard inverse-blade frame is the
normalized center projection, with the expected frame cardinality. -/
theorem shirokov_standard_frame_average (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (∑ S : Finset (Fin n),
      (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • shirokovCenterProjection n x := by
  classical
  have hpowerset : (Finset.univ : Finset (Fin n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))) := by
    ext S
    simp
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    calc
      Fintype.card (Finset (Fin n)) =
          (Finset.univ : Finset (Finset (Fin n))).card := rfl
      _ = ((Finset.univ : Finset (Fin n)).powerset).card := by rw [hpowerset]
      _ = 2 ^ n := by simp [Finset.card_powerset]
  calc
    (∑ S : Finset (Fin n),
        (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
          (((shirokovInverseBladeUnit n S)⁻¹ :
            (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
              CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
          cBlade ℝ n S := by
            change (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))),
              (shirokovInverseBladeUnit n S :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
                (((shirokovInverseBladeUnit n S)⁻¹ :
                  (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
                    CliffordAlgebra (cliffordNegSqForm ℝ n))) = _
            rw [← hpowerset]
            simp only [shirokovInverseBladeUnit_val, shirokovInverseBladeUnit_inv_val]
    _ = shirokovReynolds n x := rfl
    _ = Fintype.card (Finset (Fin n)) • shirokovCenterProjection n x := by
      change shirokovReynolds n x =
        (Fintype.card (Finset (Fin n)) : ℝ) •
          (((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x)
      rw [hcard, smul_smul]
      have hpow : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
      have hcast : ((2 ^ n : ℕ) : ℝ) = (2 ^ n : ℝ) := by norm_cast
      rw [hcast]
      have hpowReal : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [mul_inv_cancel₀ hpowReal, one_smul]

/-- The Reynolds identity transports to any frame obtained by applying a real
Clifford algebra automorphism to the standard inverse-blade frame. -/
theorem shirokov_automorphism_frame_average (n : ℕ)
    (φ : CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₐ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (∑ S : Finset (Fin n),
      (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
        (↑((Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))⁻¹) :
          CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) •
        φ (shirokovCenterProjection n (φ.symm x)) := by
  calc
    _ = ∑ S : Finset (Fin n),
        φ ((shirokovInverseBladeUnit n S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (φ.symm x) * cBlade ℝ n S) := by
            apply Finset.sum_congr rfl
            intro S hS
            change φ (shirokovInverseBladeUnit n S :
              CliffordAlgebra (cliffordNegSqForm ℝ n)) * x * φ (cBlade ℝ n S) =
              φ ((shirokovInverseBladeUnit n S :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) *
                (φ.symm x) * cBlade ℝ n S)
            simp only [map_mul, AlgEquiv.apply_symm_apply]
    _ = φ (∑ S : Finset (Fin n),
        (shirokovInverseBladeUnit n S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (φ.symm x) * cBlade ℝ n S) := by rw [map_sum]
    _ = φ (Fintype.card (Finset (Fin n)) •
        shirokovCenterProjection n (φ.symm x)) := by
          congr 1
          simpa only [shirokovInverseBladeUnit_inv_val] using
            shirokov_standard_frame_average n (φ.symm x)
    _ = Fintype.card (Finset (Fin n)) •
        φ (shirokovCenterProjection n (φ.symm x)) := by
          rw [map_nsmul]

/-- The isometry-induced Clifford automorphism sends each ordered coordinate
blade to the ordered product of the corresponding transformed frame vectors. -/
theorem shirokov_isometry_map_blade
    (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    CliffordAlgebra.equivOfIsometry e (cBlade ℝ n S) =
      shirokovIsometryFrameBlade n e S := by
  simp only [cBlade, map_list_prod, List.map_map, Function.comp_def, cGen,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  rfl

/-- An isometry-transformed frame has an independent family of all ordered
blades. This proves finite-stage basis independence for isometry-induced
frames in the negative-definite Clifford carrier. -/
theorem shirokov_isometry_frame_blades_linearIndependent (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n)) :
    LinearIndependent ℝ
      (fun S : Finset (Fin n) => shirokovIsometryFrameBlade n e S) := by
  have hstandard := shirokov_standard_blades_linearIndependent n
  have hmap := hstandard.map'
    (CliffordAlgebra.equivOfIsometry e).toLinearMap
    (LinearMap.ker_eq_bot.mpr (CliffordAlgebra.equivOfIsometry e).injective)
  convert hmap using 1
  funext S
  exact (shirokov_isometry_map_blade n e S).symm

/-- Isometry-transformed ordered blades span the whole finite-stage Clifford
algebra, by transporting the standard blade expansion through its algebra
equivalence. -/
theorem shirokov_isometry_frame_blades_span_eq_top (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n)) :
    Submodule.span ℝ
      (Set.range (fun S : Finset (Fin n) => shirokovIsometryFrameBlade n e S)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  let φ := CliffordAlgebra.equivOfIsometry e
  have hx : x = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      bladeRepr ℝ n (φ.symm x) S • shirokovIsometryFrameBlade n e S := by
    calc
      x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
      _ = φ (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          bladeRepr ℝ n (φ.symm x) S • cBlade ℝ n S) := by
            exact congrArg φ (shirokov_blade_expansion n (φ.symm x))
      _ = _ := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro S hS
            rw [map_smul, shirokov_isometry_map_blade]
  rw [hx]
  apply Submodule.sum_mem
  intro S hS
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨S, rfl⟩

/-- The isometry-transformed ordered blades form a basis of `Cl(0,n)`. This is
the full basis conclusion for frames induced by quadratic-form isometries. -/
noncomputable def shirokov_isometry_frame_blade_basis (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n)) :
    Module.Basis (Finset (Fin n)) ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
  Module.Basis.mk (shirokov_isometry_frame_blades_linearIndependent n e)
    (shirokov_isometry_frame_blades_span_eq_top n e).symm.le

@[simp] theorem shirokov_isometry_frame_blade_basis_apply (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    shirokov_isometry_frame_blade_basis n e S = shirokovIsometryFrameBlade n e S :=
  Module.Basis.mk_apply _ _ _

/-- For any real quadratic form on a finite coordinate space, an isometry
transports Mathlib's canonical Clifford blade basis to a basis. This extends
the fixed `Cl(0,n)` result to arbitrary signatures for isometry-induced frames;
it does not assert that every frame satisfying only the Clifford relations
comes from such an isometry. -/
noncomputable def shirokov_general_isometry_blade_basis {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (e : Q.IsometryEquiv Q) :
    Module.Basis (Finset (Fin n)) ℝ (CliffordAlgebra Q) :=
  (InfoGeometry.Clifford.GradedGraceContraction.cliffordBladeBasis Q).map
    (CliffordAlgebra.equivOfIsometry e).toLinearEquiv

@[simp] theorem shirokov_general_isometry_blade_basis_apply {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (e : Q.IsometryEquiv Q) (S : Finset (Fin n)) :
    shirokov_general_isometry_blade_basis Q e S =
      CliffordAlgebra.equivOfIsometry e
        (InfoGeometry.Clifford.GradedGraceContraction.cliffordBladeBasis Q S) := rfl

/-- Inverse ordered blade unit associated to a quadratic-form isometry frame. -/
noncomputable def shirokovIsometryInverseBladeUnit (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) : (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ :=
  Units.map (CliffordAlgebra.equivOfIsometry e).toMonoidHom
    (shirokovInverseBladeUnit n S)

@[simp] theorem shirokovIsometryInverseBladeUnit_val (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    (shirokovIsometryInverseBladeUnit n e S :
      CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2)) •
        shirokovIsometryFrameBlade n e S := by
  change CliffordAlgebra.equivOfIsometry e
    (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) = _
  rw [shirokovInverseBladeUnit_val, map_smul,
    shirokov_isometry_map_blade]

@[simp] theorem shirokovIsometryInverseBladeUnit_inv_val (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    (((shirokovIsometryInverseBladeUnit n e S)⁻¹ :
      (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      shirokovIsometryFrameBlade n e S := by
  change CliffordAlgebra.equivOfIsometry e
    ((((shirokovInverseBladeUnit n S)⁻¹ :
      (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
        CliffordAlgebra (cliffordNegSqForm ℝ n))) = _
  rw [shirokovInverseBladeUnit_inv_val, shirokov_isometry_map_blade]

/-- Theorem 2.2 for an automorphism-transported standard frame. The connection
coefficient is assumed grade two after pulling it back to the standard frame. -/
theorem shirokov_theorem_2_2_automorphism_frame_grade_two
    (n : ℕ)
    (φ : CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₐ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (φ.symm C) T ≠ 0 → T.card = 2) :
    (∑ S : Finset (Fin n),
      D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (↑((Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))⁻¹) :
          CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • C := by
  let transportedCenterProjection :
      CliffordAlgebra (cliffordNegSqForm ℝ n) →
        CliffordAlgebra (cliffordNegSqForm ℝ n) :=
    fun z => φ (shirokovCenterProjection n (φ.symm z))
  have haverage := shirokov_automorphism_frame_average n φ C
  have hzero : transportedCenterProjection C = 0 := by
    dsimp [transportedCenterProjection]
    rw [shirokov_center_projection_eq_zero_of_grade_two n (φ.symm C) hgrade]
    exact map_zero φ
  have hresult := shirokov_theorem_2_2_average_reduction
    (R := ℝ) (A := CliffordAlgebra (cliffordNegSqForm ℝ n))
    (ι := Finset (Fin n)) D C transportedCenterProjection
    (fun S => Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))
    hcompat (by simpa [transportedCenterProjection] using haverage)
  rw [hzero] at hresult
  simpa using hresult

/-- Theorem 2.2 for a frame induced by an isometry of the fixed quadratic
space. This exposes the moving blade units directly; the grade-two condition
is read after transport back to the standard frame. -/
theorem shirokov_theorem_2_2_isometry_frame_grade_two
    (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (shirokovIsometryInverseBladeUnit n e S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (shirokovIsometryInverseBladeUnit n e S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (shirokovIsometryInverseBladeUnit n e S :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n),
      bladeRepr ℝ n ((CliffordAlgebra.equivOfIsometry e).symm C) T ≠ 0 →
        T.card = 2) :
    (∑ S : Finset (Fin n),
      D (shirokovIsometryInverseBladeUnit n e S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (↑((shirokovIsometryInverseBladeUnit n e S)⁻¹) :
          CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • C := by
  simpa [shirokovIsometryInverseBladeUnit] using
    shirokov_theorem_2_2_automorphism_frame_grade_two n
      (CliffordAlgebra.equivOfIsometry e) D C hcompat hgrade

/-- Theorem 2.2 for the standard inverse-blade frame: compatibility and
grade-two support remove the center-projection term from the average formula.
Transport to the paper's varying dual frame is a separate result. -/
theorem shirokov_theorem_2_2_standard_frame_grade_two
    (n : ℕ)
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n C T ≠ 0 → T.card = 2) :
    (∑ S : Finset (Fin n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • C := by
  have haverage := shirokov_standard_frame_average n C
  have hzero := shirokov_center_projection_eq_zero_of_grade_two n C hgrade
  have hresult := shirokov_theorem_2_2_average_reduction
    (R := ℝ) (A := CliffordAlgebra (cliffordNegSqForm ℝ n))
    (ι := Finset (Fin n)) D C
    (shirokovCenterProjection n) (shirokovInverseBladeUnit n) hcompat haverage
  rw [hzero] at hresult
  simpa using hresult

/-- Odd-dimensional reduced Theorem 2.2 sum for the fixed standard inverse-
blade frame. Compatibility makes each derivative summand `C - u C u⁻¹`;
complementary blades have the same conjugation action. The result does not yet
transport to the paper's varying dual frame. -/
theorem shirokov_theorem_2_2_standard_frame_odd_reduced_sum
    (n : ℕ) (hn : Odd n)
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      2 • ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
        (fun S => 2 * S.card < n),
        D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (((shirokovInverseBladeUnit n S)⁻¹ :
            (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
              CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  apply shirokov_odd_complement_sum_reduction n hn
  intro S
  have hterm (T : Finset (Fin n)) :
      D (shirokovInverseBladeUnit n T : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n T)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      C - (shirokovInverseBladeUnit n T : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C *
        (((shirokovInverseBladeUnit n T)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
    rw [hcompat T]
    have huinv :
        (shirokovInverseBladeUnit n T : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (((shirokovInverseBladeUnit n T)⁻¹ :
            (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
              CliffordAlgebra (cliffordNegSqForm ℝ n)) = 1 := by
      rw [shirokovInverseBladeUnit_val, shirokovInverseBladeUnit_inv_val]
      exact (shirokov_blade_inverse_formula n T).1
    change (C * (shirokovInverseBladeUnit n T :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) -
      (shirokovInverseBladeUnit n T : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C) *
        (((shirokovInverseBladeUnit n T)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) = _
    calc
      _ = C * ((shirokovInverseBladeUnit n T :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
            (((shirokovInverseBladeUnit n T)⁻¹ :
              (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
                CliffordAlgebra (cliffordNegSqForm ℝ n))) -
          (shirokovInverseBladeUnit n T : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C *
            (((shirokovInverseBladeUnit n T)⁻¹ :
              (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) := by noncomm_ring
      _ = C - (shirokovInverseBladeUnit n T :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) * C *
            (((shirokovInverseBladeUnit n T)⁻¹ :
              (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
          congr 1
          rw [huinv, mul_one]
  rw [hterm S, hterm (Finset.univ \ S)]
  congr 1
  exact shirokov_odd_inverse_blade_conjugation_complement n hn S C

/-- Odd-dimensional standard-frame Theorem 2.2 in normalized lower-half form.
Under the grade-two condition, compatibility and complement pairing give the
reduced sum `2^(n-1) • C`. -/
theorem shirokov_theorem_2_2_standard_frame_odd_grade_two
    (n : ℕ) (hn : Odd n)
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n C T ≠ 0 → T.card = 2) :
    (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
      (fun S => 2 * S.card < n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      (2 ^ (n - 1) : ℝ) • C := by
  have hred := shirokov_theorem_2_2_standard_frame_odd_reduced_sum
    n hn D C hcompat
  have hfull := shirokov_theorem_2_2_standard_frame_grade_two n D C hcompat hgrade
  have hpowerset : (Finset.univ : Finset (Fin n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))) := by
    ext S
    simp
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    calc
      Fintype.card (Finset (Fin n)) =
          (Finset.univ : Finset (Finset (Fin n))).card := rfl
      _ = ((Finset.univ : Finset (Fin n)).powerset).card := by rw [hpowerset]
      _ = 2 ^ n := by simp
  have hcardR : (Fintype.card (Finset (Fin n)) : ℝ) = 2 ^ n := by
    exact_mod_cast hcard
  have hfull' :
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (((shirokovInverseBladeUnit n S)⁻¹ :
            (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
              CliffordAlgebra (cliffordNegSqForm ℝ n))) =
        (Fintype.card (Finset (Fin n)) : ℝ) • C := by
    calc
      _ = ∑ S : Finset (Fin n),
          D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
            (((shirokovInverseBladeUnit n S)⁻¹ :
              (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
          rw [← hpowerset]
      _ = Fintype.card (Finset (Fin n)) • C := hfull
  rcases hn with ⟨k, hk⟩
  have hnval : n = 2 * k + 1 := by omega
  have hnsub : n - 1 = 2 * k := by omega
  have hfactor : (2 : ℝ) * (2 ^ (n - 1) : ℝ) = (2 ^ n : ℝ) := by
    calc
      (2 : ℝ) * (2 ^ (n - 1) : ℝ) = 2 * (2 ^ (2 * k) : ℝ) := by
            congr 1
            exact congrArg (fun m : ℕ => (2 : ℝ) ^ m) hnsub
      _ = (2 ^ (2 * k + 1) : ℝ) := by rw [pow_succ]; ring
      _ = (2 ^ n : ℝ) := congrArg (fun m : ℕ => (2 : ℝ) ^ m) hnval.symm
  have hredR := hred
  have hmul : (2 : ℝ) •
      (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
        (fun S => 2 * S.card < n),
        D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      (2 : ℝ) • ((2 ^ (n - 1) : ℝ) • C) := by
    calc
      _ = ((Fintype.card (Finset (Fin n)) : ℝ)) • C := hredR.symm.trans hfull'
      _ = (2 ^ n : ℝ) • C := by rw [hcardR]
      _ = (2 : ℝ) • ((2 ^ (n - 1) : ℝ) • C) := by
        rw [← hfactor, smul_smul]
  exact (smul_right_injective (R := ℝ) (M := CliffordAlgebra (cliffordNegSqForm ℝ n))
    (by norm_num : (2 : ℝ) ≠ 0)) hmul

/-- Odd-dimensional lower-half formula for an algebra-automorphism-transported
frame. The derivative and grade condition are pulled back to the standard
negative-definite frame and then transported forward. -/
theorem shirokov_theorem_2_2_automorphism_frame_odd_grade_two
    (n : ℕ) (hn : Odd n)
    (φ : CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₐ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (φ.symm C) T ≠ 0 → T.card = 2) :
    (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
      (fun S => 2 * S.card < n),
      D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (↑((Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))⁻¹) :
          CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      (2 ^ (n - 1) : ℝ) • C := by
  let D' : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n) := fun x => φ.symm (D (φ x))
  let C' : CliffordAlgebra (cliffordNegSqForm ℝ n) := φ.symm C
  have hcompat' : ∀ S : Finset (Fin n),
      D' (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C' * (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C' := by
    intro S
    apply φ.injective
    simpa [D', C', map_sub, map_mul] using hcompat S
  have hstd := shirokov_theorem_2_2_standard_frame_odd_grade_two
    n hn D' C' hcompat' hgrade
  have hmap : φ ((∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
      (fun S => 2 * S.card < n),
      D' (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)))) =
      (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter
        (fun S => 2 * S.card < n),
        D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (↑((Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))⁻¹) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro S hS
    simp only [D', map_mul, AlgEquiv.apply_symm_apply, Units.coe_map,
      Units.coe_map_inv, shirokovInverseBladeUnit_inv_val]
    rfl
  have hresult := congrArg φ hstd
  rw [hmap] at hresult
  simpa [C'] using hresult

private theorem endCommutator_double_scaled (A B : FormEnd V) (r s : ℝ) :
    endCommutator A (endCommutator (r • A) (s • B)) =
      s • (r • endCommutator A (endCommutator A B)) := by
  have hinner : endCommutator (r • A) (s • B) =
      (r * s) • endCommutator A B := by
    rw [endCommutator_smul_left, endCommutator_smul_right, smul_smul]
  calc
    endCommutator A (endCommutator (r • A) (s • B)) =
        (r * s) • endCommutator A (endCommutator A B) := by
          rw [hinner, endCommutator_smul_right]
    _ = s • (r • endCommutator A (endCommutator A B)) := by
          rw [smul_smul, mul_comm]

/-- Conditional Shirokov Theorem 5.2 on the literal exterior-form Clifford
action. For a pseudo-orthonormal frame, `B = C + σ c(e_i)` has the asserted
curvature and cubic current, provided the background is flat and the scaled
frame is covariantly constant. -/
theorem shirokov_clifford_vector_yang_mills
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (D : DerivationFamily (ι := ι) (A := FormEnd V))
    (C : ι → FormEnd V) (σ : ℝ)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        commutator (C i) (σ • cartanCliffordAction g (b j))) :
    (∀ i j,
      fieldStrength D (fun k => C k + σ • cartanCliffordAction g (b k)) i j =
        -commutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) ∧
    (∀ j,
      yangMillsCurrent D (fun k => C k + σ • cartanCliffordAction g (b k))
        (fieldStrength D
          (fun k => C k + σ • cartanCliffordAction g (b k))) j =
        ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          cartanCliffordAction g (b j)) := by
  constructor
  · intro i j
    exact fieldStrength_background_plus_parallel D C
      (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel i j
  · intro j
    rw [yangMillsCurrent_background_plus_parallel D C
      (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel j]
    simpa only [InfoGeometry.Canonical.ShirokovYangMillsTransfer.commutator,
      endCommutator] using
      scaled_orthonormal_frame_double_commutator_sum b g hg horth j σ

/-- Pseudo-Euclidean version of the conditional Clifford-vector theorem. The
raised-index current acts on the raised output generator `ε j • c(e_j)`. -/
theorem shirokov_pseudo_clifford_vector_yang_mills
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (D : DerivationFamily (ι := ι) (A := FormEnd V))
    (C : ι → FormEnd V) (σ : ℝ)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        commutator (C i) (σ • cartanCliffordAction g (b j))) :
    ∀ j,
      pseudoYangMillsCurrent D ε
        (fun k => C k + σ • cartanCliffordAction g (b k))
        (fieldStrength D
          (fun k => C k + σ • cartanCliffordAction g (b k))) j =
        ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          (ε j • cartanCliffordAction g (b j)) := by
  intro j
  rw [pseudoYangMillsCurrent_background_plus_parallel D C
    (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel ε j]
  have hscale (i : ι) := endCommutator_double_scaled
    (σ • cartanCliffordAction g (b i))
    (σ • cartanCliffordAction g (b j)) (ε i) (ε j)
  have hsum :
      (∑ i : ι,
        endCommutator (σ • cartanCliffordAction g (b i))
          (endCommutator (ε i • (σ • cartanCliffordAction g (b i)))
            (ε j • (σ • cartanCliffordAction g (b j)))) : FormEnd V) =
        ε j • ∑ i : ι, ε i •
          endCommutator (σ • cartanCliffordAction g (b i))
            (endCommutator (σ • cartanCliffordAction g (b i))
              (σ • cartanCliffordAction g (b j))) := by
    calc
      _ = ∑ i : ι, ε j • (ε i •
          endCommutator (σ • cartanCliffordAction g (b i))
            (endCommutator (σ • cartanCliffordAction g (b i))
              (σ • cartanCliffordAction g (b j)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hscale i
      _ = ε j • ∑ i : ι, ε i •
          endCommutator (σ • cartanCliffordAction g (b i))
            (endCommutator (σ • cartanCliffordAction g (b i))
              (σ • cartanCliffordAction g (b j))) := by rw [Finset.smul_sum]
  change ε j • ∑ i : ι, ε i •
      endCommutator (σ • cartanCliffordAction g (b i))
        (endCommutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) =
      ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
        (ε j • cartanCliffordAction g (b j))
  rw [← hsum]
  exact scaled_pseudoOrthonormal_frame_contracted_double_commutator
    b g hg ε hε horth j σ

/-- Conditional Theorem 5.3 transfer for a frame-derived spin connection.
The frame derivative identity supplies parallelness through the metric-skew
spin lift; flatness remains an explicit hypothesis. -/
theorem shirokov_pseudo_frame_derivative_yang_mills
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (d : ι → ι → V)
    (hcompat : ∀ μ i j,
      g (d μ i) (b j) + g (b i) (d μ j) = 0)
    (D : DerivationFamily (ι := ι) (A := FormEnd V)) (σ : ℝ)
    (hflat : ∀ i j,
      D.apply i (spinConnectionFromFrameDerivative b g hg d j) -
        D.apply j (spinConnectionFromFrameDerivative b g hg d i) -
          commutator (spinConnectionFromFrameDerivative b g hg d i)
            (spinConnectionFromFrameDerivative b g hg d j) = 0)
    (hframeDerivative : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        σ • cartanCliffordAction g (d i j)) :
    (∀ i j,
      fieldStrength D
        (fun k => spinConnectionFromFrameDerivative b g hg d k +
          σ • cartanCliffordAction g (b k)) i j =
        -commutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) ∧
    (∀ j,
      pseudoYangMillsCurrent D ε
        (fun k => spinConnectionFromFrameDerivative b g hg d k +
          σ • cartanCliffordAction g (b k))
        (fieldStrength D
          (fun k => spinConnectionFromFrameDerivative b g hg d k +
            σ • cartanCliffordAction g (b k))) j =
        ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          (ε j • cartanCliffordAction g (b j))) := by
  let C := fun i => spinConnectionFromFrameDerivative b g hg d i
  have hskew (i : ι) :
      ∀ x y, g (frameDerivativeMap b (d i) x) y +
        g x (frameDerivativeMap b (d i) y) = 0 :=
    frameDerivativeMap_metricSkew b g (d i) (hcompat i)
  have hparallel : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        commutator (C i) (σ • cartanCliffordAction g (b j)) := by
    intro i j
    rw [hframeDerivative i j]
    change σ • cartanCliffordAction g (d i j) =
      endCommutator (metricSkewSpinLift b g hg
        (frameDerivativeMap b (d i)))
        (σ • cartanCliffordAction g (b j))
    rw [endCommutator_smul_right]
    rw [metricSkewSpinLift_comm_cartanCliffordAction b g hg hgsymm
      (frameDerivativeMap b (d i)) (hskew i) (b j)]
    rw [frameDerivativeMap_apply_basis]
  constructor
  · intro i j
    exact fieldStrength_background_plus_parallel D C
      (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel i j
  · exact shirokov_pseudo_clifford_vector_yang_mills b g hgsymm ε hε horth
      D C σ hflat hparallel

end InfoGeometry.Canonical.ShirokovCliffordYangMills
