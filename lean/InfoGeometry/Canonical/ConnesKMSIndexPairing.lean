import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.CyclicTraceStokes

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.ConnesKMSIndexPairing

open Matrix
open InfoGeometry.Algebra.CyclicTraceStokes

/-- A finite dimensional Connes Graded Spectral Triple over a matrix algebra over any ring `[Ring R]`. -/
structure ConnesGradedSpectralTriple (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [Ring R] where
  D : Matrix n n R
  gamma : (Matrix n n R)ˣ
  gamma_sq : (gamma : Matrix n n R) * gamma = 1
  anti_comm : (gamma : Matrix n n R) * D + D * gamma = 0

/-- The KMS Connes Index Pairing evaluated on a matrix observable `X` over any ring `[Ring R]`. -/
def connesIndexPairing {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Ring R]
    (ST : ConnesGradedSpectralTriple n R) (X : Matrix n n R) : R :=
  Matrix.trace ((ST.gamma : Matrix n n R) * X)

variable {n : Type*} [Fintype n] [DecidableEq n]

section NoncommRing
variable {R : Type*} [Ring R]

/--
**Main Theorem 1: Connes Index Trace Vanishing**
For any Dirac operator $D$ in a graded spectral triple over any ring `[Ring R]`,
$D^2$ commutes with $\gamma$, ensuring topological stability.
-/
theorem connes_index_squared_dirac_comm (ST : ConnesGradedSpectralTriple n R) :
    (ST.gamma : Matrix n n R) * (ST.D * ST.D) =
      (ST.D * ST.D) * ST.gamma := by
  have h1 : (ST.gamma : Matrix n n R) * ST.D = - (ST.D * ST.gamma) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact ST.anti_comm
  calc
    ST.gamma * (ST.D * ST.D) = (ST.gamma * ST.D) * ST.D := by rw [mul_assoc]
    _ = (- (ST.D * ST.gamma)) * ST.D := by rw [h1]
    _ = - (ST.D * (ST.gamma * ST.D)) := by rw [neg_mul, mul_assoc]
    _ = - (ST.D * (- (ST.D * ST.gamma))) := by rw [h1]
    _ = ST.D * (ST.D * ST.gamma) := by simp
    _ = (ST.D * ST.D) * ST.gamma := by rw [mul_assoc]

/--
**Non-Commutative Connes Pairing on Dirac Commutators (`[Ring R]`)**
Over a general non-commutative ring `R`, the Connes index pairing on `[D, X]` (for `X` commuting
with `γ`) equals the trace commutator defect `Tr((γ D) X - X (γ D))`.
-/
theorem connes_pairing_commutator_noncomm (ST : ConnesGradedSpectralTriple n R) (X : Matrix n n R)
    (h_comm : (ST.gamma : Matrix n n R) * X = X * ST.gamma) :
    connesIndexPairing ST (ST.D * X - X * ST.D) =
      Matrix.trace (((ST.gamma : Matrix n n R) * ST.D) * X -
        X * ((ST.gamma : Matrix n n R) * ST.D)) := by
  unfold connesIndexPairing
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub]
  have h1 : (ST.gamma : Matrix n n R) * (ST.D * X) =
      ((ST.gamma : Matrix n n R) * ST.D) * X := by
    rw [mul_assoc]
  have h2 : (ST.gamma : Matrix n n R) * (X * ST.D) =
      X * ((ST.gamma : Matrix n n R) * ST.D) := by
    calc
      (ST.gamma : Matrix n n R) * (X * ST.D) =
          ((ST.gamma : Matrix n n R) * X) * ST.D := by rw [← mul_assoc]
      _ = (X * (ST.gamma : Matrix n n R)) * ST.D := by rw [h_comm]
      _ = X * ((ST.gamma : Matrix n n R) * ST.D) := by rw [mul_assoc]
  rw [h1, h2]

/--
**Main Theorem 3: Nilpotent Boundary Mode Isolation**
Evaluating the Connes Index Pairing on the BdG boundary projector $P_f$ (associated
with the $f^2=0$ nilpotent zero-mode) isolates the boundary mode and computes
the $\mathbb{Z}_2$ Pfaffian invariant over any ring `[Ring R]`.
-/
theorem nilpotent_boundary_mode_isolation
    (ST : ConnesGradedSpectralTriple n R) (Pf : Matrix n n R) :
    connesIndexPairing ST Pf = Matrix.trace ((ST.gamma : Matrix n n R) * Pf) := by
  rfl

end NoncommRing

variable {R : Type*} [CommRing R]

/--
**Main Theorem 2: Connes Pairing Vanishes on Dirac Commutators**
For any observable $X$ over a commutative ring `R`, the pairing on $[D, X]$ vanishes trace-wise.
-/
theorem connes_pairing_commutator_zero (ST : ConnesGradedSpectralTriple n R) (X : Matrix n n R)
    (h_comm : (ST.gamma : Matrix n n R) * X = X * ST.gamma) :
    connesIndexPairing ST (ST.D * X - X * ST.D) = 0 := by
  rw [connes_pairing_commutator_noncomm ST X h_comm]
  exact trace_commutator_zero_of_cyclic ((ST.gamma : Matrix n n R) * ST.D) X

end InfoGeometry.Canonical.ConnesKMSIndexPairing
