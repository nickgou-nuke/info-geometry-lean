import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace InfoGeometry.OperatorAlgebra.FiniteRelativeOrientation

variable {n R : Type*} [Fintype n] [CommRing R]

def relativeBoltzmannAction
    (logActual logReference X : Matrix n n R) : Matrix n n R :=
  -(logActual * X) + X * logReference

def positiveRelativeInformationAction
    (logActual logReference X : Matrix n n R) : Matrix n n R :=
  -(logReference * X) + X * logActual

def relativeInformationTrace
    (actual logActual logReference : Matrix n n R) : R :=
  Matrix.trace (actual * (logActual - logReference))

theorem left_mul_commutes_right_mul
    (A B X : Matrix n n R) :
    A * (X * B) = (A * X) * B := by
  rw [Matrix.mul_assoc]

theorem relativeBoltzmannAction_eq_neg_leftLog_add_rightLog
    (logActual logReference X : Matrix n n R) :
    relativeBoltzmannAction logActual logReference X =
      -(logActual * X) + X * logReference :=
  rfl

theorem positiveRelativeInformationAction_eq_reversedBoltzmannAction
    (logActual logReference X : Matrix n n R) :
    positiveRelativeInformationAction logActual logReference X =
      relativeBoltzmannAction logReference logActual X :=
  rfl

theorem relativeBoltzmann_trace_readout
    (xi actual logActual logReference : Matrix n n R)
    (hxi : xi * xi = actual) :
    Matrix.trace
        (xi * relativeBoltzmannAction logActual logReference xi) =
      -relativeInformationTrace actual logActual logReference := by
  calc
    Matrix.trace
        (xi * relativeBoltzmannAction logActual logReference xi)
        = Matrix.trace (xi * (-(logActual * xi))) +
            Matrix.trace (xi * (xi * logReference)) := by
              rw [relativeBoltzmannAction, mul_add, Matrix.trace_add]
    _ = -Matrix.trace (xi * (logActual * xi)) +
          Matrix.trace ((xi * xi) * logReference) := by
            simp [Matrix.mul_assoc]
    _ = -Matrix.trace ((logActual * xi) * xi) +
          Matrix.trace (actual * logReference) := by
            rw [Matrix.trace_mul_comm xi (logActual * xi), hxi]
    _ = -Matrix.trace (logActual * actual) +
          Matrix.trace (actual * logReference) := by
            rw [Matrix.mul_assoc, hxi]
    _ = -Matrix.trace (actual * logActual) +
          Matrix.trace (actual * logReference) := by
            rw [Matrix.trace_mul_comm logActual actual]
    _ = -relativeInformationTrace actual logActual logReference := by
          rw [relativeInformationTrace, mul_sub, Matrix.trace_sub]
          ring

theorem positiveRelativeInformation_trace_readout
    (xi actual logActual logReference : Matrix n n R)
    (hxi : xi * xi = actual) :
    Matrix.trace
        (xi * positiveRelativeInformationAction logActual logReference xi) =
      relativeInformationTrace actual logActual logReference := by
  rw [positiveRelativeInformationAction_eq_reversedBoltzmannAction]
  rw [relativeBoltzmann_trace_readout xi actual logReference logActual hxi]
  rw [relativeInformationTrace, relativeInformationTrace, mul_sub, mul_sub,
    Matrix.trace_sub, Matrix.trace_sub]
  ring

theorem ordered_pair_trace_sign
    (xi actual logActual logReference : Matrix n n R)
    (hxi : xi * xi = actual) :
    Matrix.trace
        (xi * relativeBoltzmannAction logActual logReference xi) =
      -Matrix.trace
        (xi * positiveRelativeInformationAction logActual logReference xi) := by
  rw [relativeBoltzmann_trace_readout xi actual logActual logReference hxi]
  rw [positiveRelativeInformation_trace_readout xi actual logActual logReference hxi]

end InfoGeometry.OperatorAlgebra.FiniteRelativeOrientation
