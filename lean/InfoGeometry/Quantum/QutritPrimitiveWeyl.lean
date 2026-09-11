import InfoGeometry.Quantum.QutritBraidIncidenceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AharonovBohmConcreteVortex

/-!
# Primitive qutrit Weyl pair

This module specializes the existing qutrit clock/shift construction to the
repository's canonical primitive cubic root of unity. It strengthens cube
identities to exact-order-three statements by proving that neither the first
nor the second power is the identity.
-/

noncomputable section

namespace InfoGeometry.Quantum.QutritBraidIncidenceBridge

open InfoGeometry.Topology.Parafermion
open InfoGeometry.Physics.HestenesCuntzPhaseSpace
open InfoGeometry.Physics.MD014TriSpinZ3Projectors

/-- The standard qutrit clock, specialized to the existing primitive cubic root. -/
def qutritPrimitiveClock : QutritMatrix :=
  qutritGeneralizedPauliZ omega

/-- The canonical nontrivial qutrit Weyl pair. -/
def qutritPrimitiveWeylPair : FiniteWeylPair 3 QutritMatrix :=
  qutritWeylPair omega omega_cube_eq_one

/-- The Weyl scalar in the canonical qutrit pair is genuinely primitive. -/
theorem qutritPrimitiveWeylPair_q_isPrimitiveRoot :
    IsPrimitiveRoot qutritPrimitiveWeylPair.q 3 := by
  simpa [qutritPrimitiveWeylPair, qutritWeylPair] using omega_isPrimitiveRoot

@[simp] theorem qutritPrimitiveClock_cube : qutritPrimitiveClock ^ 3 = 1 := by
  simpa [qutritPrimitiveClock, pow_succ, mul_assoc] using
    qutritGeneralizedPauliZ_cube_identity omega omega_cube_eq_one

@[simp] theorem qutritPrimitiveClock_ne_one : qutritPrimitiveClock ≠ 1 := by
  intro h
  have hentry := congrArg (fun A : QutritMatrix => A 1 1) h
  apply omega_ne_one
  simpa [qutritPrimitiveClock, qutritGeneralizedPauliZ, sectorPhase,
    sectorProjector0, sectorProjector1, sectorProjector2] using hentry

@[simp] theorem qutritPrimitiveClock_sq_ne_one : qutritPrimitiveClock ^ 2 ≠ 1 := by
  intro h
  have hentry := congrArg (fun A : QutritMatrix => A 1 1) h
  have hω2 : omega ^ 2 ≠ 1 :=
    omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  apply hω2
  simpa [qutritPrimitiveClock, qutritGeneralizedPauliZ, sectorPhase,
    sectorProjector0, sectorProjector1, sectorProjector2, pow_two,
    Matrix.mul_apply, Fin.sum_univ_three] using hentry

/-- The primitive qutrit clock has exact multiplicative order three. -/
theorem qutritPrimitiveClock_exact_order_three :
    qutritPrimitiveClock ^ 3 = 1 ∧
      qutritPrimitiveClock ≠ 1 ∧ qutritPrimitiveClock ^ 2 ≠ 1 :=
  ⟨qutritPrimitiveClock_cube, qutritPrimitiveClock_ne_one,
    qutritPrimitiveClock_sq_ne_one⟩

@[simp] theorem qutritGeneralizedPauliX_ne_one : qutritGeneralizedPauliX ≠ 1 := by
  intro h
  have hentry := congrArg (fun A : QutritMatrix => A 1 0) h
  simp [qutritGeneralizedPauliX, qutritShiftMatrix] at hentry

@[simp] theorem qutritGeneralizedPauliX_sq_ne_one : qutritGeneralizedPauliX ^ 2 ≠ 1 := by
  intro h
  have hentry := congrArg (fun A : QutritMatrix => A 2 0) h
  simp [qutritGeneralizedPauliX, qutritShiftMatrix, pow_two,
    Matrix.mul_apply, Fin.sum_univ_three] at hentry

/-- The generalized qutrit shift has exact multiplicative order three. -/
theorem qutritGeneralizedPauliX_exact_order_three :
    qutritGeneralizedPauliX ^ 3 = 1 ∧
      qutritGeneralizedPauliX ≠ 1 ∧ qutritGeneralizedPauliX ^ 2 ≠ 1 := by
  refine ⟨?_, qutritGeneralizedPauliX_ne_one, qutritGeneralizedPauliX_sq_ne_one⟩
  simpa [pow_succ, mul_assoc] using qutritGeneralizedPauliX_cube_identity

/-- The canonical primitive clock and shift satisfy `ZX = ω XZ`. -/
theorem qutritPrimitiveClock_mul_X :
    qutritPrimitiveClock * qutritGeneralizedPauliX =
      omega • (qutritGeneralizedPauliX * qutritPrimitiveClock) :=
  qutritGeneralizedPauliZ_mul_X omega omega_cube_eq_one

end InfoGeometry.Quantum.QutritBraidIncidenceBridge
