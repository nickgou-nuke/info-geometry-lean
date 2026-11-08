import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.QuaternionPauliRealForm

/-! Associative quaternionic frames and their native Pauli action. -/

namespace InfoGeometry.Canonical.QuaternionicOperatorFrame

structure Frame (A : Type*) [Ring A] where
  i : A
  j : A
  k : A
  i_sq : i * i = -(1 : A)
  j_sq : j * j = -(1 : A)
  k_sq : k * k = -(1 : A)
  ij : i * j = k
  jk : j * k = i
  ki : k * i = j

variable {A : Type*} [Ring A]

theorem Frame.ji (Q : Frame A) : Q.j * Q.i = -Q.k := by
  calc
    Q.j * Q.i = (Q.k * Q.i) * Q.i := by rw [Q.ki]
    _ = Q.k * (Q.i * Q.i) := by rw [mul_assoc]
    _ = Q.k * (-(1 : A)) := by rw [Q.i_sq]
    _ = -Q.k := by simp

theorem Frame.kj (Q : Frame A) : Q.k * Q.j = -Q.i := by
  calc
    Q.k * Q.j = (Q.i * Q.j) * Q.j := by rw [Q.ij]
    _ = Q.i * (Q.j * Q.j) := by rw [mul_assoc]
    _ = Q.i * (-(1 : A)) := by rw [Q.j_sq]
    _ = -Q.i := by simp

abbrev PauliMatrix := InfoGeometry.Clifford.QuaternionPauliRealForm.Mat2C
abbrev PauliSpinor := InfoGeometry.Algebra.FiniteSpin.Vec2C
abbrev PauliOperator := PauliSpinor →ₗ[ℂ] PauliSpinor

noncomputable def action (A : PauliMatrix) : PauliOperator := Matrix.toLin' A

theorem action_mul (A B : PauliMatrix) :
    (action A).comp (action B) = action (A * B) := by
  change (Matrix.toLin' A).comp (Matrix.toLin' B) = Matrix.toLin' (A * B)
  rw [← Matrix.toLin'_mul]

theorem action_sq_of (A : PauliMatrix) (hA : A * A = -(1 : PauliMatrix)) :
    (action A).comp (action A) = -(LinearMap.id : PauliOperator) := by
  have hcomp : (Matrix.toLin' A).comp (Matrix.toLin' A) =
      Matrix.toLin' (-(1 : PauliMatrix)) := by
    rw [← Matrix.toLin'_mul, hA]
  simpa [action] using hcomp

theorem pauli_i_sq :
    (action InfoGeometry.Clifford.QuaternionPauliRealForm.qi).comp
      (action InfoGeometry.Clifford.QuaternionPauliRealForm.qi) =
        -(LinearMap.id : PauliOperator) := by
  exact action_sq_of _ InfoGeometry.Clifford.QuaternionPauliRealForm.qi_sq

end InfoGeometry.Canonical.QuaternionicOperatorFrame
