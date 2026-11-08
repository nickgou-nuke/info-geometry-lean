import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import InfoGeometry.Canonical.FiniteSuperchargeIndex

/-!
# The indefinite coupling identity and its lack of positive coercivity

The proposed block Hamiltonian is self-adjoint for the indefinite metric
`diag(1,-1)` when its diagonal Hamiltonians are Hermitian. This is an exact
matrix realization, not a second definition of the repository's Krein carrier.
The real coupled system `x'=v y, y'=v x` preserves `x²-y²`, yet has an
exponentially growing null solution. Off-diagonal coupling therefore does
not by itself provide a positive energy estimate.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KreinCouplingControl

open Matrix

theorem block_krein_adjoint_identity {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (D : Matrix κ κ ℂ) (V : Matrix ι κ ℂ)
    (hA : Aᴴ = A) (hD : Dᴴ = D) :
    (fromBlocks A V (-Vᴴ) (-D))ᴴ * fromBlocks 1 0 0 (-1) =
      fromBlocks 1 0 0 (-1) * fromBlocks A V (-Vᴴ) (-D) := by
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hA, hD]

/-- Exact derivative of the conserved indefinite quadratic form. -/
theorem coupled_krein_rate_zero (v x y : ℝ) :
    2 * x * (v * y) - 2 * y * (v * x) = 0 := by ring

/-- The coupled equations have a growing trajectory on their null cone. -/
theorem coupled_null_solution (v t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (v * s))
      (v * Real.exp (v * t)) t ∧
    Real.exp (v * t) ^ 2 - Real.exp (v * t) ^ 2 = 0 := by
  constructor
  · simpa [mul_comm] using ((hasDerivAt_id t).const_mul v).exp
  · ring

/-- Its positive quadratic energy has strictly positive instantaneous production. -/
theorem positive_energy_rate_on_null_mode {v x : ℝ} (hv : 0 < v) (hx : x ≠ 0) :
    0 < 2 * x * (v * x) + 2 * x * (v * x) := by
  have h := mul_pos hv (sq_pos_of_ne_zero hx)
  nlinarith

/-- A conserved zero Krein quadratic value gives no bound on positive size. -/
theorem null_quadratic_has_unbounded_positive_size (B : ℝ) :
    ∃ x y : ℝ, x ^ 2 - y ^ 2 = 0 ∧ B < x ^ 2 + y ^ 2 := by
  refine ⟨B ^ 2 + 1, B ^ 2 + 1, by ring, ?_⟩
  nlinarith [sq_nonneg B, sq_nonneg (B - 1), sq_nonneg (B ^ 2)]

/-- Every linear kernel contains zero, so the proposed unnormalized kernel
distance bound already fails for the singular set `{0}`. -/
theorem no_positive_distance_for_entire_kernel
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : X →ₗ[ℝ] X) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ LinearMap.ker D, ε ≤ dist x 0 := by
  rintro ⟨ε, hε, hbound⟩
  have hz := hbound 0 (LinearMap.map_zero D)
  simp only [dist_self] at hz
  exact (not_le_of_gt hε) hz

/-- Even after normalization, an index of one does not exclude a singular
locus that contains the zero mode. Here the locus is the singleton constant
unit vector. No relation between an index and an arbitrary locus is automatic. -/
theorem nonzero_index_with_normalized_singular_zero_mode :
    InfoGeometry.Canonical.FiniteSuperchargeIndex.wittenIndex
      (InfoGeometry.Canonical.FiniteSuperchargeIndex.zeroSupercharge 1 0) = 1 ∧
    ∃ x : Fin 1 → ℝ,
      x ∈ LinearMap.ker
        (InfoGeometry.Canonical.FiniteSuperchargeIndex.zeroSupercharge 1 0).qPlus ∧
      ‖x‖ = 1 ∧ dist x (fun _ => 1) = 0 := by
  constructor
  · rw [InfoGeometry.Canonical.FiniteSuperchargeIndex.zeroSupercharge_wittenIndex]
    norm_num
  · refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · simp [InfoGeometry.Canonical.FiniteSuperchargeIndex.zeroSupercharge]
    · simp
    · simp

end InfoGeometry.OperatorAlgebra.KreinCouplingControl
