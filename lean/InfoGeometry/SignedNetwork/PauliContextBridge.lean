/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Algebra.FiniteSpinAlgebra
namespace InfoGeometry.SignedNetwork.PauliContextBridge
noncomputable section
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open scoped Matrix
abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2C
def contextProjector (x y z : ℝ) : Mat2 := PauliParavector.pauliMatrix ⟨1/2,x/2,y/2,z/2⟩
theorem contextProjector_trace (x y z : ℝ) : Matrix.trace (contextProjector x y z) = 1 := by
  simp [contextProjector, PauliParavector.trace_pauliMatrix_eq_two_energy]

/-- The maximally mixed qubit state used by the PR-facing selection packet. -/
def mixed : Mat2 := (1 / 2 : ℂ) • (1 : Mat2)

theorem contextProjector_self_adjoint (nx ny nz : ℝ) :
    (contextProjector nx ny nz)ᴴ = contextProjector nx ny nz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [contextProjector, PauliParavector.pauliMatrix, Matrix.conjTranspose_apply] <;> ring

theorem contextProjector_idempotent (nx ny nz : ℝ)
    (hn : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    contextProjector nx ny nz * contextProjector nx ny nz =
      contextProjector nx ny nz := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [contextProjector, PauliParavector.pauliMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hn]

/-- The existing determinant theorem supplies the singularity of the rank-one carrier. -/
theorem contextProjector_det (nx ny nz : ℝ)
    (hn : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    Matrix.det (contextProjector nx ny nz) = 0 := by
  rw [contextProjector, PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]
  have hreal :
      (PauliParavector.mk (1/2) (nx/2) (ny/2) (nz/2)).minkowskiNormSq = 0 := by
    dsimp [PauliParavector.minkowskiNormSq]
    nlinarith [hn]
  rw [hreal]
  simp

/-- The actual selective update, with its nonunit success probability exposed. -/
theorem context_selection_packet (nx ny nz : ℝ)
    (hn : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    Matrix.trace (contextProjector nx ny nz * mixed * contextProjector nx ny nz) = 1/2 ∧
      (Matrix.trace (contextProjector nx ny nz * mixed * contextProjector nx ny nz))⁻¹ •
        (contextProjector nx ny nz * mixed * contextProjector nx ny nz) =
          contextProjector nx ny nz := by
  have hbranch :
      contextProjector nx ny nz * mixed * contextProjector nx ny nz =
        (1 / 2 : ℂ) • contextProjector nx ny nz := by
    simp [mixed, mul_smul_comm, mul_one, smul_mul_assoc,
      contextProjector_idempotent nx ny nz hn]
  constructor
  · rw [hbranch, Matrix.trace_smul, contextProjector_trace]
    simp
  · rw [hbranch]
    rw [show Matrix.trace ((1 / 2 : ℂ) • contextProjector nx ny nz) = 1 / 2 by
      rw [Matrix.trace_smul, contextProjector_trace]
      simp]
    rw [smul_smul]
    norm_num
end
end InfoGeometry.SignedNetwork.PauliContextBridge
