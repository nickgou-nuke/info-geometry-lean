import Mathlib
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Canonical.QuaternionEmbedding

/-! Finite Clifford-parity identities for the native Dirac carrier.  The
vector and axial channels are kept distinct; this is not a differential
curvature construction. -/
namespace InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma

noncomputable section

abbrev ComplexFourVector := Fin 4 → ℂ

def minkowskiQuadratic (A : ComplexFourVector) : ℂ :=
  A 0 ^ 2 - A 1 ^ 2 - A 2 ^ 2 - A 3 ^ 2

def slash (A : ComplexFourVector) : DiracMatrix :=
  A 0 • gamma0 + A 1 • gamma1 + A 2 • gamma2 + A 3 • gamma3

def axialSlash (A : ComplexFourVector) : DiracMatrix := slash A * gamma5

def oddPotential (A B : ComplexFourVector) : DiracMatrix :=
  slash A + axialSlash B

def mixedBivectorResidue (A B : ComplexFourVector) : DiracMatrix :=
  (slash A * slash B - slash B * slash A) * gamma5

def IsCliffordOdd (X : DiracMatrix) : Prop := gamma5 * X + X * gamma5 = 0

def IsCliffordEven (X : DiracMatrix) : Prop := gamma5 * X = X * gamma5

theorem gamma5_mul_slash_eq_neg (A : ComplexFourVector) :
    gamma5 * slash A = -(slash A * gamma5) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem slash_isCliffordOdd (A : ComplexFourVector) :
    IsCliffordOdd (slash A) := by
  unfold IsCliffordOdd
  rw [gamma5_mul_slash_eq_neg]
  simp

theorem slash_sq (A : ComplexFourVector) :
    slash A * slash A = minkowskiQuadratic A • (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, minkowskiQuadratic, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem axialSlash_sq (A : ComplexFourVector) :
    axialSlash A * axialSlash A = -(minkowskiQuadratic A) • (1 : DiracMatrix) := by
  unfold axialSlash
  calc
    (slash A * gamma5) * (slash A * gamma5) =
        slash A * (gamma5 * slash A) * gamma5 := by noncomm_ring
    _ = slash A * (-(slash A * gamma5)) * gamma5 := by
      rw [gamma5_mul_slash_eq_neg]
    _ = -(slash A * slash A) * (gamma5 * gamma5) := by noncomm_ring
    _ = -(minkowskiQuadratic A) • (1 : DiracMatrix) := by
      rw [slash_sq, gamma5_mul_self]
      simp [smul_eq_mul]

theorem oddPotential_sq_decomposition (A B : ComplexFourVector) :
    oddPotential A B * oddPotential A B =
      (minkowskiQuadratic A - minkowskiQuadratic B) • (1 : DiracMatrix) +
        mixedBivectorResidue A B := by
  unfold oddPotential mixedBivectorResidue axialSlash
  have hswap := gamma5_mul_slash_eq_neg A
  have haxial := axialSlash_sq B
  unfold axialSlash at haxial
  calc
    (slash A + slash B * gamma5) * (slash A + slash B * gamma5) =
        slash A * slash A + (slash A * slash B - slash B * slash A) * gamma5 +
          (slash B * gamma5) * (slash B * gamma5) := by
      noncomm_ring [hswap]
    _ = minkowskiQuadratic A • (1 : DiracMatrix) +
        (slash A * slash B - slash B * slash A) * gamma5 +
          (-(minkowskiQuadratic B) • (1 : DiracMatrix)) := by
      rw [slash_sq, haxial]
    _ = (minkowskiQuadratic A - minkowskiQuadratic B) • (1 : DiracMatrix) +
        (slash A * slash B - slash B * slash A) * gamma5 := by
      module

theorem odd_square_is_even (X : DiracMatrix) (hX : IsCliffordOdd X) :
    IsCliffordEven (X * X) := by
  unfold IsCliffordEven at *
  have h : gamma5 * X = -(X * gamma5) := eq_neg_of_add_eq_zero_left hX
  calc
    gamma5 * (X * X) = (gamma5 * X) * X := by rw [mul_assoc]
    _ = (-(X * gamma5)) * X := by rw [h]
    _ = X * (X * gamma5) := by
      rw [neg_mul, mul_assoc, h, mul_neg, neg_neg]
    _ = (X * X) * gamma5 := by exact (mul_assoc X X gamma5).symm

theorem axialSlash_isCliffordOdd (B : ComplexFourVector) :
    IsCliffordOdd (axialSlash B) := by
  unfold IsCliffordOdd axialSlash
  have hswap := gamma5_mul_slash_eq_neg B
  calc
    gamma5 * (slash B * gamma5) + slash B * gamma5 * gamma5 =
        (gamma5 * slash B) * gamma5 + slash B * gamma5 * gamma5 := by
          simp only [mul_assoc]
    _ = (-(slash B * gamma5)) * gamma5 + slash B * gamma5 * gamma5 := by
          rw [hswap]
    _ = 0 := by
      simp only [neg_mul, gamma5_mul_self, mul_one]
      abel

theorem oddPotential_isCliffordOdd (A B : ComplexFourVector) :
    IsCliffordOdd (oddPotential A B) := by
  unfold IsCliffordOdd oddPotential
  have hA := slash_isCliffordOdd A
  have hB := axialSlash_isCliffordOdd B
  unfold IsCliffordOdd at hA hB
  calc
    gamma5 * (slash A + axialSlash B) + (slash A + axialSlash B) * gamma5 =
        (gamma5 * slash A + slash A * gamma5) +
          (gamma5 * axialSlash B + axialSlash B * gamma5) := by
            noncomm_ring
    _ = 0 := by rw [hA, hB, add_zero]

theorem oddPotential_sq_isCliffordEven (A B : ComplexFourVector) :
    IsCliffordEven (oddPotential A B * oddPotential A B) := by
  unfold IsCliffordEven
  have hodd := oddPotential_isCliffordOdd A B
  exact odd_square_is_even (oddPotential A B) hodd

theorem pureVector_square_is_scalar (A : ComplexFourVector) :
    oddPotential A 0 * oddPotential A 0 =
      minkowskiQuadratic A • (1 : DiracMatrix) := by
  have hzero : axialSlash (0 : ComplexFourVector) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [axialSlash, slash]
  rw [oddPotential, hzero, add_zero]
  exact slash_sq A

open InfoGeometry.Canonical.QuaternionEmbedding

theorem commute_quaternionic_third_of_first_two
    (N : DiracMatrix)
    (hi : Commute N quat_i)
    (hj : Commute N quat_j) :
    Commute N quat_k := by
  rw [← quat_ij_eq_k]
  exact hi.mul_right hj

def quaternionicBivectorCombination (a b c : ℂ) : DiracMatrix :=
  a • quat_i + b • quat_j + c • quat_k

theorem commute_quaternionicBivectorCombination_of_first_two
    (N : DiracMatrix)
    (hi : Commute N quat_i)
    (hj : Commute N quat_j)
    (a b c : ℂ) :
    Commute N (quaternionicBivectorCombination a b c) := by
  have hk := commute_quaternionic_third_of_first_two N hi hj
  unfold quaternionicBivectorCombination
  simpa [add_assoc] using
    (hi.smul_right a).add_right
      ((hj.smul_right b).add_right (hk.smul_right c))

end
end InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
