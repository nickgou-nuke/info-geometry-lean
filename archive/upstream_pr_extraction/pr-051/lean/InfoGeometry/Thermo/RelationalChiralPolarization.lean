import InfoGeometry.Thermo.FiniteMatrix

/-!
# Relational finite chiral polarization

This file keeps the chiral readout at the finite matrix level.  A frame is an
involutory matrix, the polarization is its trace pairing with a state-like
matrix, and covariance is simultaneous conjugation.  No positivity,
renormalisation, or stress-energy law is assumed here.
-/

namespace InfoGeometry.Thermo

open Matrix

variable {n : ℕ}

abbrev FiniteOperator := Matrix (Fin n) (Fin n) ℝ

/-- A finite chiral frame is an involution. -/
structure ChiralFrame where
  gamma : FiniteOperator (n := n)
  sq : gamma * gamma = 1

/-- The relational chiral polarization of a pair `(rho, frame)`. -/
def relationalPolarization (rho : FiniteOperator (n := n))
    (frame : ChiralFrame (n := n)) : ℝ :=
  Matrix.trace (rho * frame.gamma)

@[simp]
theorem relationalPolarization_zero (frame : ChiralFrame (n := n)) :
    relationalPolarization (0 : FiniteOperator (n := n)) frame = 0 := by
  simp [relationalPolarization]

/-- The elementary simultaneous transport of a state and a frame. -/
def simultaneousTransport (u v : FiniteOperator (n := n))
    (a : FiniteOperator (n := n)) : FiniteOperator (n := n) :=
  u * a * v

theorem relationalPolarization_simultaneousTransport
    (rho gamma u v : FiniteOperator (n := n))
    (hvu : v * u = 1) :
    Matrix.trace (simultaneousTransport u v rho *
      simultaneousTransport u v gamma) = Matrix.trace (rho * gamma) := by
  unfold simultaneousTransport
  calc
    Matrix.trace ((u * rho * v) * (u * gamma * v)) =
        Matrix.trace (u * (rho * (v * u)) * gamma * v) := by
          simp [mul_assoc]
    _ = Matrix.trace (u * (rho * gamma) * v) := by simp [hvu, mul_assoc]
    _ = Matrix.trace (v * u * (rho * gamma)) := by
          simpa [mul_assoc] using Matrix.trace_mul_cycle u (rho * gamma) v
    _ = Matrix.trace (rho * gamma) := by rw [hvu]; simp

theorem relationalPolarization_simultaneousTransport_frame
    (rho : FiniteOperator (n := n)) (frame : ChiralFrame (n := n))
    (u v : FiniteOperator (n := n))
    (hvu : v * u = 1) :
    Matrix.trace (simultaneousTransport u v rho *
      simultaneousTransport u v frame.gamma) =
      relationalPolarization rho frame := by
  exact relationalPolarization_simultaneousTransport rho frame.gamma u v hvu

/-- Fixed-frame modular mismatch: the transported frame minus the original. -/
def modularFrameMismatch (u v : FiniteOperator (n := n))
    (frame : ChiralFrame (n := n)) : FiniteOperator (n := n) :=
  simultaneousTransport u v frame.gamma - frame.gamma

theorem modularFrameMismatch_zero_of_commute
    (u v : FiniteOperator (n := n)) (frame : ChiralFrame (n := n))
    (huv : u * v = 1)
    (hcomm : u * frame.gamma = frame.gamma * u) :
    modularFrameMismatch u v frame = 0 := by
  unfold modularFrameMismatch simultaneousTransport
  calc
    u * frame.gamma * v - frame.gamma =
        frame.gamma * u * v - frame.gamma := by rw [hcomm]
    _ = frame.gamma - frame.gamma := by rw [mul_assoc, huv, mul_one]
    _ = 0 := sub_self _

theorem relationalPolarization_mismatch_readout
    (rho : FiniteOperator (n := n)) (u v : FiniteOperator (n := n))
    (frame : ChiralFrame (n := n)) :
    relationalPolarization (simultaneousTransport u v rho) frame -
      relationalPolarization rho frame =
      Matrix.trace ((simultaneousTransport u v rho - rho) * frame.gamma) := by
  unfold relationalPolarization simultaneousTransport
  rw [sub_mul, Matrix.trace_sub]

end InfoGeometry.Thermo
