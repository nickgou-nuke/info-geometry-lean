import Mathlib

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n]

abbrev TraceOperatorSpace (n : Type*) := Matrix n n ℝ

def tracePairingNative (X Y : TraceOperatorSpace n) : ℝ := Matrix.trace (X * Y)

def leftActionNative (A X : TraceOperatorSpace n) : TraceOperatorSpace n := A * X
def rightActionNative (A X : TraceOperatorSpace n) : TraceOperatorSpace n := X * A

def jordanActionNative (A X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  leftActionNative A X + rightActionNative A X

def commutatorActionNative (A X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  leftActionNative A X - rightActionNative A X

theorem tracePairing_native_comm (X Y : TraceOperatorSpace n) :
    tracePairingNative X Y = tracePairingNative Y X := by
  unfold tracePairingNative
  exact Matrix.trace_mul_comm X Y

theorem commutatorActionNative_mul (A X Y : TraceOperatorSpace n) :
    commutatorActionNative A (X * Y) =
      commutatorActionNative A X * Y + X * commutatorActionNative A Y := by
  dsimp [commutatorActionNative, leftActionNative, rightActionNative]
  noncomm_ring

theorem commutatorActionNative_jacobi (A B X : TraceOperatorSpace n) :
    commutatorActionNative A (commutatorActionNative B X) -
        commutatorActionNative B (commutatorActionNative A X) =
      commutatorActionNative (A * B - B * A) X := by
  dsimp [commutatorActionNative, leftActionNative, rightActionNative]
  noncomm_ring

theorem left_right_tracePairing_native (A X Y : TraceOperatorSpace n) :
    tracePairingNative (leftActionNative A X) Y =
      tracePairingNative X (rightActionNative A Y) := by
  dsimp [tracePairingNative, leftActionNative, rightActionNative]
  calc
    Matrix.trace ((A * X) * Y) = Matrix.trace (A * (X * Y)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((X * Y) * A) := Matrix.trace_mul_comm A (X * Y)
    _ = Matrix.trace (X * (Y * A)) := by rw [Matrix.mul_assoc]

theorem jordan_tracePairing_native (A X Y : TraceOperatorSpace n) :
    tracePairingNative (jordanActionNative A X) Y =
      tracePairingNative X (jordanActionNative A Y) := by
  dsimp [tracePairingNative, jordanActionNative, leftActionNative, rightActionNative]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add]
  have h₁ : Matrix.trace (A * X * Y) = Matrix.trace (X * (Y * A)) := by
    calc
      Matrix.trace (A * X * Y) = Matrix.trace (A * (X * Y)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((X * Y) * A) := Matrix.trace_mul_comm A (X * Y)
      _ = Matrix.trace (X * (Y * A)) := by rw [Matrix.mul_assoc]
  have h₂ : Matrix.trace (X * A * Y) = Matrix.trace (X * (A * Y)) := by
    rw [Matrix.mul_assoc]
  rw [h₁, h₂]
  exact add_comm _ _

theorem commutator_tracePairing_native (A X Y : TraceOperatorSpace n) :
    tracePairingNative (commutatorActionNative A X) Y =
      - tracePairingNative X (commutatorActionNative A Y) := by
  dsimp [tracePairingNative, commutatorActionNative, leftActionNative, rightActionNative]
  change Matrix.trace ((A * X - X * A) * Y) =
    -Matrix.trace (X * (A * Y - Y * A))
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub]
  have h₁ : Matrix.trace (A * X * Y) = Matrix.trace (X * (Y * A)) := by
    calc
      Matrix.trace (A * X * Y) = Matrix.trace (A * (X * Y)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((X * Y) * A) := Matrix.trace_mul_comm A (X * Y)
      _ = Matrix.trace (X * (Y * A)) := by rw [Matrix.mul_assoc]
  have h₂ : Matrix.trace (X * A * Y) = Matrix.trace (X * (A * Y)) := by
    rw [Matrix.mul_assoc]
  rw [h₁, h₂]
  abel

theorem commutator_tracePairing_energyOrthogonal (H X : TraceOperatorSpace n) :
    tracePairingNative H (commutatorActionNative H X) = 0 := by
  dsimp [tracePairingNative, commutatorActionNative,
    leftActionNative, rightActionNative]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  have h : Matrix.trace (H * (X * H)) = Matrix.trace (H * (H * X)) := by
    calc
      Matrix.trace (H * (X * H)) = Matrix.trace ((H * X) * H) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace (H * (H * X)) := Matrix.trace_mul_comm (H * X) H
  rw [h]
  exact sub_self _

end InfoGeometry.Physics
