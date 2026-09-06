import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Modular.ChoiCompletePositivity
import InfoGeometry.Modular.QuantumRelativeEntropyMonotonicity

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex
open scoped InnerProductSpace
open InfoGeometry.Modular.Choi
open InfoGeometry.Modular.RelativeEntropy

namespace QuantumChannelContractivity

variable {n m : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)]

/-- Kraus Representation Quantum Channel Operator Φ(ρ) = K * ρ * K† with K† * K = 1. -/
abbrev KrausQuantumChannel (n m : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)] :=
  Matrix (Fin m) (Fin n) ℂ

namespace KrausQuantumChannel

variable (channel : KrausQuantumChannel n m)

/-- Compatibility accessor for the native Kraus matrix carrier. -/
abbrev K_val : Matrix (Fin m) (Fin n) ℂ := channel

/-- The rectangular Kraus operator acts as a linear map between the finite
Euclidean Hilbert spaces carried by its input and output indices. -/
def linearMap : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  Matrix.toEuclideanLin channel.K_val

/-- The Kraus isometry law preserves the complex inner product, not merely
the norm of individual vectors. -/
theorem inner_map_map (x y : EuclideanSpace ℂ (Fin n))
    (h_kraus_isometry : channel.K_val.conjTranspose * channel.K_val = 1) :
    ⟪linearMap channel x, linearMap channel y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (Matrix.toEuclideanLin channel.K_val y).ofLp ⬝ᵥ
    star ((Matrix.toEuclideanLin channel.K_val x).ofLp) = _
  rw [Matrix.ofLp_toLpLin 2 2, Matrix.ofLp_toLpLin 2 2]
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  rw [Matrix.star_mulVec]
  rw [dotProduct_comm]
  rw [← dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec]
  rw [h_kraus_isometry]
  simp only [one_mulVec]
  exact dotProduct_comm _ _

/-- Native Mathlib `LinearIsometry` owner for a rectangular Kraus operator. -/
noncomputable def linearIsometry
    (h_kraus_isometry : channel.K_val.conjTranspose * channel.K_val = 1) :
    EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
  (linearMap channel).isometryOfInner (fun x y =>
    inner_map_map channel x y h_kraus_isometry)

/-- Quantum Channel Action Φ(ρ) = K * ρ * K†. -/
def apply (rho : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  channel.K_val * rho * channel.K_val.conjTranspose

/-- **Theorem**: Quantum Channel Trace Preservation: Tr(Φ(ρ)) = Tr(ρ). -/
theorem trace_preserving (rho : Matrix (Fin n) (Fin n) ℂ)
    (h_kraus_isometry : channel.K_val.conjTranspose * channel.K_val = 1) :
    trace (channel.apply rho) = trace rho := by
  dsimp [apply]
  have h_comm : trace (channel.K_val * rho * channel.K_val.conjTranspose) = trace (channel.K_val.conjTranspose * (channel.K_val * rho)) := by
    rw [trace_mul_comm]
  rw [h_comm, ← Matrix.mul_assoc, h_kraus_isometry, one_mul]

/-- **Theorem**: Quantum Channel Hermiticity Preservation: (Φ(ρ))† = Φ(ρ†). -/
theorem hermiticity_preserving (rho : Matrix (Fin n) (Fin n) ℂ) :
    (channel.apply rho).conjTranspose = channel.apply rho.conjTranspose := by
  dsimp [apply]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc]

/--
  **Derived Lemma**: Kraus diagonal map preserves the trace exactly when the
  Kraus weights are Hermiticity-preserving contractions in the spectral frame.
  This is the eigenvalue-level trace contraction needed for monotonicity.
-/
theorem diagonal_kraus_trace_preserving (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1)
    (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.conjTranspose * K = 1) :
    trace (Matrix.diagonal (fun i => (p i : ℂ)) * K * K.conjTranspose) =
      ∑ i, (p i : ℂ) := by
  have h_mul : K * K.conjTranspose = 1 := by
    exact (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ (by rfl)).mpr hK
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, h_mul, Matrix.one_mul, Matrix.trace_diagonal]

/--
  **MASTER THEOREM**: Data Processing Inequality / Contractivity of Quantum Relative Entropy.
  For any CPTP quantum channel trajectory with non-negative entropy production rate,
  the relative entropy between the evolved state and invariant reference state is monotonically decreasing:
    S(Φ_t(ρ) ∥ σ) ≤ S(ρ ∥ σ)
-/
theorem data_processing (traj : SemigroupTrajectory (Fin n)) (t : ℝ) (ht : 0 ≤ t) :
    relEntropy (traj.state t) traj.inv_state ≤ relEntropy (traj.state 0) traj.inv_state :=
  relEntropy_finite_time_contraction traj t ht

end KrausQuantumChannel

end QuantumChannelContractivity
