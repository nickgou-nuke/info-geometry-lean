/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FreeEnergyDissipationRate
import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-!
# BKM mobility in the finite matrix free-energy rate

The finite Kubo--Mori transform is transported to matrices through the
existing matrix/operator equivalence.  On self-adjoint gradients its trace
quadratic is the diagonal BKM pairing, so the existing free-energy rate
formula gives dissipation when the gradient commutes with the matrix appearing
in the reversible commutator term, which makes that trace contribution vanish.
No self-adjointness or unitary-flow claim is made about this matrix.
The density defining this mobility is a fixed reference density; this file
does not identify it with the evolving density in the dissipative system.
`freeEnergyRate` here is the owner’s algebraic trace functional; no
differentiable state trajectory or trajectory-level monotonicity is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BKMOnsagerMobilityBridge

open Matrix
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

private theorem matrixOp_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    CblinfunMatrix.matrixOp (c • A) =
      c • CblinfunMatrix.matrixOp A := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [CblinfunMatrix.matrixOp]

private theorem matrixOp_add (A B : Matrix (Fin n) (Fin n) ℂ) :
    CblinfunMatrix.matrixOp (A + B) =
      CblinfunMatrix.matrixOp A + CblinfunMatrix.matrixOp B := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [CblinfunMatrix.matrixOp]

/-- The Kubo--Mori transform as a complex-linear mobility on the matrix
carrier used by `MetriplecticDissipativeSystem`. -/
noncomputable def matrixKuboMoriMobility
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun A :=
    CblinfunMatrix.matrixOfOp
      (D.kuboMoriTransform (CblinfunMatrix.matrixOp A))
  map_add' A B := by
    rw [matrixOp_add]
    change CblinfunMatrix.matrixOfOp
      (D.kuboMoriTransformCLM h (CblinfunMatrix.matrixOp A +
        CblinfunMatrix.matrixOp B)) = _
    rw [(D.kuboMoriTransformCLM h).map_add,
      ← D.kuboMoriTransformCLM_apply h (CblinfunMatrix.matrixOp A),
      ← D.kuboMoriTransformCLM_apply h (CblinfunMatrix.matrixOp B),
      CblinfunMatrix.matrixOfOp_add]
  map_smul' c A := by
    rw [matrixOp_smul]
    change CblinfunMatrix.matrixOfOp
      (D.kuboMoriTransformCLM h (c • CblinfunMatrix.matrixOp A)) = _
    rw [(D.kuboMoriTransformCLM h).map_smul,
      ← D.kuboMoriTransformCLM_apply h (CblinfunMatrix.matrixOp A),
      matrixOfOp_complex_smul]
    simp only [RingHom.id_apply]

/-- The transported BKM mobility has trace quadratic equal to the finite BKM
pairing evaluated on the adjoint matrix, for every matrix. -/
theorem matrixKuboMoriMobility_trace_eq_bkm
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (star A * matrixKuboMoriMobility D h A) =
      D.kuboMoriPairing (star (CblinfunMatrix.matrixOp A))
        (star (CblinfunMatrix.matrixOp A)) := by
  have h_matrix_star :
      CblinfunMatrix.matrixOfOp (star (CblinfunMatrix.matrixOp A)) = star A := by
    change CblinfunMatrix.matrixOfOp
      (ContinuousLinearMap.adjoint (CblinfunMatrix.matrixOp A)) = _
    rw [CblinfunMatrix.matrixOfOp_adjoint,
      CblinfunMatrix.matrixOfOp_matrixOp, ← star_eq_conjTranspose]
  rw [D.kuboMoriPairing_eq_trace_kuboMoriTransform
    (star (CblinfunMatrix.matrixOp A))
    (star (CblinfunMatrix.matrixOp A)) h]
  simp only [star_star]
  calc
    Matrix.trace (star A * matrixKuboMoriMobility D h A) =
        finiteOperatorTrace
          (star (CblinfunMatrix.matrixOp A) *
            D.kuboMoriTransform (CblinfunMatrix.matrixOp A)) := by
      unfold finiteOperatorTrace matrixKuboMoriMobility
      change Matrix.trace (star A *
          CblinfunMatrix.matrixOfOp
            (D.kuboMoriTransform (CblinfunMatrix.matrixOp A))) =
        Matrix.trace (CblinfunMatrix.matrixOfOp
          ((star (CblinfunMatrix.matrixOp A)).comp
            (D.kuboMoriTransform (CblinfunMatrix.matrixOp A))))
      rw [CblinfunMatrix.matrixOfOp_comp, h_matrix_star]
    _ = finiteOperatorTrace
        (D.kuboMoriTransform (CblinfunMatrix.matrixOp A) *
          star (CblinfunMatrix.matrixOp A)) := finiteOperatorTrace_mul_comm _ _

/-- The transported matrix mobility has a nonnegative trace quadratic on all
matrices. This is the matrix-carrier consequence of positivity of the existing
finite Kubo--Mori pairing applied to the adjoint matrix. -/
theorem matrixKuboMoriMobility_trace_nonneg
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (Matrix.trace (star A * matrixKuboMoriMobility D h A)).re := by
  rw [matrixKuboMoriMobility_trace_eq_bkm D h A]
  exact D.kuboMoriPairing_self_re_nonneg
    (star (CblinfunMatrix.matrixOp A)) h

/-- A fixed-reference BKM Onsager map makes the owner's algebraic matrix rate
nonpositive for a self-adjoint gradient that commutes with the matrix in the
reversible commutator term. This does not assert that this matrix is
self-adjoint or that the flow is unitary. The reference density `D` is not
asserted to be the current density `sys.rho`. -/
theorem freeEnergy_rate_nonpos_of_matrixKuboMoriMobility
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (sys : MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : star A = A)
    (hgrad : sys.grad_F = A)
    (hmob : ∀ X, sys.Onsager X = matrixKuboMoriMobility D h X)
    (hcomm : A * sys.H = sys.H * A) :
    MetriplecticDissipation.freeEnergyRate sys ≤ 0 := by
  have h_diss :
      ∀ B : Matrix (Fin n) (Fin n) ℂ,
        0 ≤ (trace (star B * sys.Onsager B)).re := by
    intro B
    rw [hmob]
    exact matrixKuboMoriMobility_trace_nonneg D h B
  have htrace_comm :
      trace (A * (sys.H * sys.rho - sys.rho * sys.H)) = 0 := by
    rw [mul_sub, trace_sub]
    have hcyclic :
        trace (A * (sys.H * sys.rho)) =
          trace (A * (sys.rho * sys.H)) := by
      calc
        trace (A * (sys.H * sys.rho)) = trace (sys.rho * (A * sys.H)) := by
          rw [← mul_assoc]
          exact Matrix.trace_mul_comm (A * sys.H) sys.rho
        _ = trace (sys.rho * (sys.H * A)) := by rw [hcomm]
        _ = trace ((sys.H * A) * sys.rho) :=
          Matrix.trace_mul_comm sys.rho (sys.H * A)
        _ = trace (sys.H * (A * sys.rho)) := by rw [mul_assoc]
        _ = trace ((A * sys.rho) * sys.H) :=
          Matrix.trace_mul_comm sys.H (A * sys.rho)
        _ = trace (A * (sys.rho * sys.H)) := by rw [mul_assoc]
    rw [hcyclic]
    exact sub_self _
  have hrev_zero :
      (trace (star sys.grad_F *
        (- Complex.I • (sys.H * sys.rho - sys.rho * sys.H)))).re = 0 := by
    calc
      _ = ((-Complex.I) *
          trace (A * (sys.H * sys.rho - sys.rho * sys.H))).re := by
        rw [hgrad, hA, Matrix.mul_smul, Matrix.trace_smul]
        simp only [smul_eq_mul]
      _ = 0 := by rw [htrace_comm]; simp
  exact MetriplecticDissipation.freeEnergy_rate_nonpos sys h_diss hrev_zero

/-- The same finite matrix BKM mobility dissipates the algebraic free-energy
rate when the Hamiltonian commutes with the state. In this case the reversible
commutator is zero independently of whether the gradient commutes with the
Hamiltonian. -/
theorem freeEnergy_rate_nonpos_of_matrixKuboMoriMobility_of_commuting_state
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (sys : MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (hmob : ∀ X, sys.Onsager X = matrixKuboMoriMobility D h X)
    (hHrho : sys.H * sys.rho = sys.rho * sys.H) :
    MetriplecticDissipation.freeEnergyRate sys ≤ 0 := by
  have h_diss :
      ∀ B : Matrix (Fin n) (Fin n) ℂ,
        0 ≤ (trace (star B * sys.Onsager B)).re := by
    intro B
    rw [hmob]
    exact matrixKuboMoriMobility_trace_nonneg D h B
  have hrev_zero :
      (trace (star sys.grad_F *
        (- Complex.I • (sys.H * sys.rho - sys.rho * sys.H)))).re = 0 := by
    rw [hHrho]
    simp
  exact MetriplecticDissipation.freeEnergy_rate_nonpos sys h_diss hrev_zero

end InfoGeometry.Canonical.BKMOnsagerMobilityBridge

end
