import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex
open scoped InnerProductSpace

namespace QuantumChannelContractivity

variable {n m : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)]

/-- Kraus Representation Quantum Channel Operator Φ(ρ) = K * ρ * K† with K† * K = 1. -/
structure KrausQuantumChannel (n m : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)] where
  K_val : Matrix (Fin m) (Fin n) ℂ

namespace KrausQuantumChannel

variable (channel : KrausQuantumChannel n m)

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

end KrausQuantumChannel

end QuantumChannelContractivity
