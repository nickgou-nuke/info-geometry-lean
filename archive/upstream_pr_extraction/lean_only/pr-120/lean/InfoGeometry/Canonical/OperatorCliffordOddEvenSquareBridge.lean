import Mathlib.Tactic
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Canonical.QuaternionEmbedding

/-!
# InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge

Finite Clifford-parity owner for the Pauli/Dirac operator lift.

This file separates two structures that should not be conflated:

* exterior Clifford degree `Λ^0 ⊕ ... ⊕ Λ^4`, represented here only through
  the concrete Dirac matrices and the `γ5` parity involution;
* the independent tripotent/TKK five-grading used elsewhere in the repository.

For a complex four-vector `A`, the concrete slash operator is

`A̸ = A₀ γ⁰ + A₁ γ¹ + A₂ γ² + A₃ γ³`.

It is odd with respect to `γ5`, and its square is exactly the Minkowski
quadratic scalar.  The axial operator `B̸ γ5` is also odd.  For the combined
odd operator

`D(A,B) = A̸ + B̸ γ5`,

the square is even and splits into a scalar channel plus the explicit mixed
commutator channel

`(A̸ B̸ - B̸ A̸) γ5`.

This is the finite algebraic precursor of a Weitzenböck/Lichnerowicz curvature
term.  No differential connection or geometric curvature tensor is asserted
here.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma

/-- Concrete complex four-vector coordinates. -/
abbrev ComplexFourVector := Fin 4 → ℂ

/-- Minkowski quadratic form with signature `(+---)`. -/
def minkowskiQuadratic (A : ComplexFourVector) : ℂ :=
  A 0 ^ 2 - A 1 ^ 2 - A 2 ^ 2 - A 3 ^ 2

/-- Vector Clifford embedding `A ↦ A̸`. -/
def slash (A : ComplexFourVector) : DiracMatrix :=
  A 0 • gamma0 + A 1 • gamma1 + A 2 • gamma2 + A 3 • gamma3

/-- Axial-vector Clifford embedding `B ↦ B̸ γ5`. -/
def axialSlash (B : ComplexFourVector) : DiracMatrix :=
  slash B * gamma5

/-- Combined vector plus axial-vector odd operator. -/
def oddPotential (A B : ComplexFourVector) : DiracMatrix :=
  slash A + axialSlash B

/-- `γ5`-oddness, the finite matrix form of odd Clifford parity. -/
def IsCliffordOdd (X : DiracMatrix) : Prop :=
  gamma5 * X + X * gamma5 = 0

/-- `γ5`-evenness, the finite matrix form of even Clifford parity. -/
def IsCliffordEven (X : DiracMatrix) : Prop :=
  gamma5 * X = X * gamma5

/-- The vector slash operator anticommutes with `γ5`. -/
theorem gamma5_mul_slash_eq_neg
    (A : ComplexFourVector) :
    gamma5 * slash A = -(slash A * gamma5) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- Every vector slash operator is Clifford-odd. -/
theorem slash_isCliffordOdd (A : ComplexFourVector) :
    IsCliffordOdd (slash A) := by
  unfold IsCliffordOdd
  rw [gamma5_mul_slash_eq_neg]
  simp

/-- Every axial-vector slash operator is also Clifford-odd. -/
theorem axialSlash_isCliffordOdd (B : ComplexFourVector) :
    IsCliffordOdd (axialSlash B) := by
  unfold IsCliffordOdd axialSlash
  have hswap := gamma5_mul_slash_eq_neg B
  noncomm_ring [gamma5_mul_self, hswap]

/-- The full vector plus axial-vector potential is Clifford-odd. -/
theorem oddPotential_isCliffordOdd
    (A B : ComplexFourVector) :
    IsCliffordOdd (oddPotential A B) := by
  unfold IsCliffordOdd oddPotential
  have hA := slash_isCliffordOdd A
  have hB := axialSlash_isCliffordOdd B
  unfold IsCliffordOdd at hA hB
  noncomm_ring [hA, hB]

/-- Dirac linearization of the Minkowski quadratic form. -/
theorem slash_sq (A : ComplexFourVector) :
    slash A * slash A =
      minkowskiQuadratic A • (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, minkowskiQuadratic,
      gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_sq] <;>
    ring

/-- Squaring an axial slash reverses the vector quadratic sign because
`γ5` anticommutes with vectors and satisfies `γ5² = 1`. -/
theorem axialSlash_sq (B : ComplexFourVector) :
    axialSlash B * axialSlash B =
      -(minkowskiQuadratic B) • (1 : DiracMatrix) := by
  unfold axialSlash
  calc
    (slash B * gamma5) * (slash B * gamma5)
        = slash B * (gamma5 * slash B) * gamma5 := by
            noncomm_ring
    _ = slash B * (-(slash B * gamma5)) * gamma5 := by
          rw [gamma5_mul_slash_eq_neg]
    _ = -(slash B * slash B) * (gamma5 * gamma5) := by
          noncomm_ring
    _ = -(minkowskiQuadratic B • (1 : DiracMatrix)) := by
          rw [slash_sq, gamma5_mul_self]
          simp
    _ = -(minkowskiQuadratic B) • (1 : DiracMatrix) := by
          module

/-- Mixed vector/axial residue in the square of the odd operator. -/
def mixedBivectorResidue
    (A B : ComplexFourVector) : DiracMatrix :=
  (slash A * slash B - slash B * slash A) * gamma5

/-- Exact square decomposition of a vector plus axial-vector odd operator.

The first two terms are scalar Clifford channels.  The final term is built
from the commutator of two vector Clifford elements and is therefore the
finite bivector/pseudobivector residue. -/
theorem oddPotential_sq_decomposition
    (A B : ComplexFourVector) :
    oddPotential A B * oddPotential A B =
      (minkowskiQuadratic A - minkowskiQuadratic B) •
          (1 : DiracMatrix) +
        mixedBivectorResidue A B := by
  unfold oddPotential mixedBivectorResidue axialSlash
  have hswap := gamma5_mul_slash_eq_neg A
  have haxial := axialSlash_sq B
  unfold axialSlash at haxial
  calc
    (slash A + slash B * gamma5) *
        (slash A + slash B * gamma5) =
      slash A * slash A +
        (slash A * slash B - slash B * slash A) * gamma5 +
        (slash B * gamma5) * (slash B * gamma5) := by
          noncomm_ring [hswap]
    _ = minkowskiQuadratic A • (1 : DiracMatrix) +
        (slash A * slash B - slash B * slash A) * gamma5 +
        (-(minkowskiQuadratic B) • (1 : DiracMatrix)) := by
          rw [slash_sq, haxial]
    _ = (minkowskiQuadratic A - minkowskiQuadratic B) •
          (1 : DiracMatrix) +
        (slash A * slash B - slash B * slash A) * gamma5 := by
          module

/-- The square of the combined odd potential is Clifford-even. -/
theorem oddPotential_sq_isCliffordEven
    (A B : ComplexFourVector) :
    IsCliffordEven (oddPotential A B * oddPotential A B) := by
  unfold IsCliffordEven
  have hodd := oddPotential_isCliffordOdd A B
  unfold IsCliffordOdd at hodd
  have hanti :
      gamma5 * oddPotential A B =
        -(oddPotential A B * gamma5) := by
    exact eq_neg_of_add_eq_zero_left hodd
  noncomm_ring [hanti]

/-- Pure vector specialization: the odd square collapses completely to the
Grade-0 scalar channel. -/
theorem pureVector_square_is_scalar
    (A : ComplexFourVector) :
    oddPotential A 0 * oddPotential A 0 =
      minkowskiQuadratic A • (1 : DiracMatrix) := by
  have hzero : axialSlash (0 : ComplexFourVector) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [axialSlash, slash]
  rw [oddPotential, hzero, add_zero]
  exact slash_sq A

/-! ## Quaternionic spatial-bivector packet -/

open InfoGeometry.Canonical.QuaternionEmbedding

/-- The repository quaternion units are concrete spatial Dirac bivectors. -/
theorem quaternionic_spatial_bivector_packet :
    quat_i = gamma2 * gamma3 ∧
      quat_j = gamma3 * gamma1 ∧
      quat_k = gamma1 * gamma2 ∧
      quat_i * quat_i = -(1 : DiracMatrix) ∧
      quat_j * quat_j = -(1 : DiracMatrix) ∧
      quat_k * quat_k = -(1 : DiracMatrix) ∧
      quat_i * quat_j = quat_k := by
  exact ⟨rfl, rfl, rfl,
    quat_i_sq, quat_j_sq, quat_k_sq, quat_ij_eq_k⟩

/-- An operator commuting with two quaternionic generators also commutes with
 their product, hence with the third generator. -/
theorem commute_quaternionic_third_of_first_two
    (N : DiracMatrix)
    (hi : Commute N quat_i)
    (hj : Commute N quat_j) :
    Commute N quat_k := by
  rw [← quat_ij_eq_k]
  exact hi.mul_right hj

/-- Complex linear combinations of the three spatial quaternionic bivectors. -/
def quaternionicBivectorCombination
    (a b c : ℂ) : DiracMatrix :=
  a • quat_i + b • quat_j + c • quat_k

/-- Commuting with the first two quaternionic generators protects the full
three-dimensional spatial-bivector span.  This is the theorem-supported core
of the proposed `N`-intertwining statement; no self-duality label is needed. -/
theorem commute_quaternionicBivectorCombination_of_first_two
    (N : DiracMatrix)
    (hi : Commute N quat_i)
    (hj : Commute N quat_j)
    (a b c : ℂ) :
    Commute N (quaternionicBivectorCombination a b c) := by
  have hk : Commute N quat_k :=
    commute_quaternionic_third_of_first_two N hi hj
  unfold quaternionicBivectorCombination
  simpa [add_assoc] using
    (hi.smul_right a).add_right
      ((hj.smul_right b).add_right (hk.smul_right c))

end InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
