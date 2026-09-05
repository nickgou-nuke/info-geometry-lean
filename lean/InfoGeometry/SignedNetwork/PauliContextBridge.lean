import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.SignedNetwork.CoherenceAndProjection

/-!
# Context projector in the repository's existing Pauli representation

This is a representation-level bridge, not a second definition of the Pauli
matrices. The four coefficients below are density-matrix readouts, not assumed
spacetime positions. The unit-vector condition supplies a Hermitian trace-one
idempotent. Conditioning the mixed state on it is a separate selective update.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.PauliContextBridge

open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.SignedNetwork.CoherenceAndProjection
open scoped Matrix

/-- `(I + nx sigma1 + ny sigma2 + nz sigma3)/2`, using the existing soldering map. -/
def contextProjector (nx ny nz : ℝ) : Mat2 :=
  PauliParavector.pauliMatrix ⟨1 / 2, nx / 2, ny / 2, nz / 2⟩

theorem contextProjector_trace (nx ny nz : ℝ) :
    Matrix.trace (contextProjector nx ny nz) = 1 := by
  rw [contextProjector, PauliParavector.trace_pauliMatrix_eq_two_energy]
  norm_num

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
  exact ⟨selected_mixed_probability _ (contextProjector_idempotent nx ny nz hn)
      (contextProjector_trace nx ny nz),
    selected_mixed_normalized _ (contextProjector_idempotent nx ny nz hn)
      (contextProjector_trace nx ny nz)⟩

end InfoGeometry.SignedNetwork.PauliContextBridge
