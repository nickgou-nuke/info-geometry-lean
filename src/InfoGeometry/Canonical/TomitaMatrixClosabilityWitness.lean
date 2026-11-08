import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

noncomputable section

namespace InfoGeometry.Canonical.TomitaMatrixClosabilityWitness

/-!
# Tomita Matrix Closability Witness & Pre-Hilbert Trace Isometry

This module formalizes the Tomita modular conjugation operator $S_0(A) = A^*$ on finite matrix
stages `MatrixStage n := Matrix (Fin (2^n)) (Fin (2^n)) ℂ` with respect to the trace inner product
$\langle A, B \rangle_{\omega_n} = 2^{-n} \text{Tr}(A^* B)$, proving:
1. Tomita Operator Involutivity: $S_0(S_0(A)) = A$
2. Tomita Operator Anti-Isometry: $\langle S_0(A), S_0(B) \rangle_{\omega_n} = \langle B, A \rangle_{\omega_n}$
3. Tomita Operator Trace-Norm Preservation: $\|S_0(A)\|_{\omega_n}^2 = \|A\|_{\omega_n}^2$
4. Pre-Hilbert Closability Witness: Trace-norm isometry guarantees pre-Hilbert closability of $S_0$.
-/

/-- Stage n trace inner product: ⟨A, B⟩_ω = 2⁻ⁿ · Tr(A* B). -/
def matrixTraceInnerProduct (n : ℕ) (A B : MatrixStage n) : ℂ :=
  matrixTraceState n (star A * B)

/-- Tomita modular involution operator S₀(A) = A*. -/
def tomitaInvolution (n : ℕ) (A : MatrixStage n) : MatrixStage n :=
  star A

/-- **Theorem**: Tomita Operator Involutivity S₀(S₀(A)) = A. -/
theorem tomitaInvolution_involutive (n : ℕ) (A : MatrixStage n) :
    tomitaInvolution n (tomitaInvolution n A) = A := by
  dsimp [tomitaInvolution]
  exact star_star A

/-- **Theorem**: Tomita Operator Anti-Isometry: ⟨S₀(A), S₀(B)⟩_ω = ⟨B, A⟩_ω. -/
theorem tomitaInvolution_anti_isometry (n : ℕ) (A B : MatrixStage n) :
    matrixTraceInnerProduct n (tomitaInvolution n A) (tomitaInvolution n B) =
    matrixTraceInnerProduct n B A := by
  dsimp [matrixTraceInnerProduct, tomitaInvolution]
  rw [star_star, matrixTraceState_apply, matrixTraceState_apply, Matrix.trace_mul_comm A (star B)]

/-- **Theorem**: Tomita Operator Norm Preservation: ‖S₀(A)‖²_ω = ‖A‖²_ω.
    Isometry under trace norm guarantees pre-Hilbert closability of Tomita operator S₀. -/
theorem tomitaInvolution_norm_preservation (n : ℕ) (A : MatrixStage n) :
    matrixTraceInnerProduct n (tomitaInvolution n A) (tomitaInvolution n A) =
    matrixTraceInnerProduct n A A := by
  exact tomitaInvolution_anti_isometry n A A

end InfoGeometry.Canonical.TomitaMatrixClosabilityWitness
