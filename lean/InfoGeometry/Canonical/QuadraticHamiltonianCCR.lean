import InfoGeometry.Canonical.QuadraticHamiltonianCoordinates
import InfoGeometry.Physics.SplitCliffordAlgebras

/-!
# The quadratic CCR closure behind the three Hamiltonians

Section V, equation (5.1), of arXiv:2610.08437v1. All products are in an
associative algebra: analytic unbounded operators require a separately proved
common invariant domain. The native bracket is the associative ring bracket.
The existing `SplitClifford.CCRPair` is reused, not replaced by a CAR pair.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuadraticHamiltonian

section BracketIdentities
variable {A : Type*} [Ring A]

private theorem bracket_mul_right (x y z : A) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

private theorem bracket_mul_left (x y z : A) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ + ⁅x, z⁆ * y := by
  simp only [Ring.lie_def]
  noncomm_ring

end BracketIdentities

section Quantum
variable {A : Type*} [Ring A] [Algebra ℂ A]
attribute [local instance] LieRing.ofAssociativeRing
variable (q p : A) (hqp : ⁅q, p⁆ = Complex.I • (1 : A))

include hqp

private theorem reverse_ccr : ⁅p, q⁆ = (-Complex.I) • (1 : A) := by
  calc
    ⁅p, q⁆ = -⁅q, p⁆ := by simp only [Ring.lie_def]; abel
    _ = (-Complex.I) • (1 : A) := by rw [hqp, neg_smul]

theorem H0_comm_q : ⁅H0 q p, q⁆ = (-2 * Complex.I) • p := by
  simp only [H0, add_lie, bracket_mul_left, reverse_ccr q p hqp, lie_self,
    mul_zero, zero_mul, add_zero, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, mul_one, one_mul]
  module

theorem H0_comm_p : ⁅H0 q p, p⁆ = (2 * Complex.I) • q := by
  simp only [H0, add_lie, bracket_mul_left, hqp, lie_self,
    mul_zero, zero_mul, zero_add, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, mul_one, one_mul]
  module

theorem H1_comm_q : ⁅H1 q p, q⁆ = (-2 * Complex.I) • q := by
  simp only [H1, add_lie, bracket_mul_left, reverse_ccr q p hqp, lie_self,
    mul_zero, zero_mul, add_zero, zero_add, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, mul_one, one_mul]
  module

theorem H1_comm_p : ⁅H1 q p, p⁆ = (2 * Complex.I) • p := by
  simp only [H1, add_lie, bracket_mul_left, hqp, lie_self,
    mul_zero, zero_mul, add_zero, zero_add, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, mul_one, one_mul]
  module

theorem H2_comm_q : ⁅H2 q p, q⁆ = (-2 * Complex.I) • p := by
  simp only [H2, sub_lie, bracket_mul_left, reverse_ccr q p hqp, lie_self,
    mul_zero, zero_mul, add_zero, sub_zero, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, mul_one, one_mul]
  module

theorem H2_comm_p : ⁅H2 q p, p⁆ = (-2 * Complex.I) • q := by
  simp only [H2, sub_lie, bracket_mul_left, hqp, lie_self,
    mul_zero, zero_mul, add_zero, zero_sub, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, mul_one, one_mul]
  module

/-- First equation (5.1), in exactly the paper's normalization. -/
theorem H0_comm_H1 : ⁅H0 q p, H1 q p⁆ = (-4 * Complex.I) • H2 q p := by
  simp only [H1, lie_add, bracket_mul_right, H0_comm_q q p hqp,
    H0_comm_p q p hqp, H2, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  module

theorem H1_comm_H2 : ⁅H1 q p, H2 q p⁆ = (4 * Complex.I) • H0 q p := by
  simp only [H2, lie_sub, bracket_mul_right, H1_comm_q q p hqp,
    H1_comm_p q p hqp, H0, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  module

theorem H2_comm_H0 : ⁅H2 q p, H0 q p⁆ = (-4 * Complex.I) • H1 q p := by
  simp only [H0, lie_add, bracket_mul_right, H2_comm_q q p hqp,
    H2_comm_p q p hqp, H1, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  module

omit hqp

def K1 (q p : A) : A := (1 / 4 : ℂ) • H1 q p

def K2 (q p : A) : A := (1 / 4 : ℂ) • H2 q p

def K3 (q p : A) : A := (-1 / 4 : ℂ) • H0 q p

/-- The three scaled Lie relations (5.3), without an adjoint or spectrum claim. -/
include hqp in
theorem su11_relations :
    ⁅K1 q p, K2 q p⁆ = (-Complex.I) • K3 q p ∧
    ⁅K2 q p, K3 q p⁆ = Complex.I • K1 q p ∧
    ⁅K3 q p, K1 q p⁆ = Complex.I • K2 q p := by
  constructor
  · simp only [K1, K2, K3, smul_lie, lie_smul, H1_comm_H2 q p hqp, smul_smul]
    module
  constructor
  · simp only [K1, K2, K3, smul_lie, lie_smul, H2_comm_H0 q p hqp, smul_smul]
    module
  · simp only [K1, K2, K3, smul_lie, lie_smul, H0_comm_H1 q p hqp, smul_smul]
    module

/-- Convert the existing exact CCR pair to `[q,p]=i`, with explicit signs. -/
theorem ccrPair_position_momentum (C : SplitClifford.CCRPair A) :
    ⁅C.cre, (-Complex.I) • C.ann⁆ = Complex.I • (1 : A) := by
  have h : C.cre * C.ann - C.ann * C.cre = -(1 : A) := by
    calc
      _ = -(C.ann * C.cre - C.cre * C.ann) := by abel
      _ = _ := by rw [C.commutator]
  simp only [Ring.lie_def, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub, h]
  simp

end Quantum

end InfoGeometry.Canonical.QuadraticHamiltonian
