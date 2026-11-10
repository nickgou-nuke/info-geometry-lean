/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.FinitePartialTrace
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Full-matrix boundary purification and a conditional Gibbs specialization

The ordered rectangular amplitude `S` determines the vector `vec Sᵀ` and its
positive outer-product operator. Its existing second-factor partial trace is
exactly `S * Sᴴ`. The vector norm below is the native Euclidean `L²` norm.
For a positive matrix of trace one, native CFC supplies the square-root
amplitude, a positive trace-one purification, and an idempotent outer product.

The Gibbs construction uses the supplied Hermitian matrix and real parameter.
It explicitly normalizes the existing, unnormalized CFC Gibbs weight. The
doubled generator acts as the ordered commutator on amplitudes; its vanishing
for the Gibbs amplitude is derived from functional-calculus commutation.
No conclusion about arbitrary doubled systems or physical sectors is asserted.
-/

noncomputable section

namespace InfoGeometry.Quantum.MatrixBoundaryPurification

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

section Amplitudes

variable {m n : ℕ}

/-- Row-first vectorization equipped with the native Euclidean norm. -/
def amplitudeVector (S : Matrix (Fin m) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin m × Fin n) :=
  WithLp.toLp 2 (vec Sᵀ)

/-- The bipartite outer product of the full rectangular amplitude. -/
def amplitudeDensity (S : Matrix (Fin m) (Fin n) ℂ) : BipartiteOperator m n :=
  vecMulVec (vec Sᵀ) (star (vec Sᵀ))

theorem amplitudeDensity_posSemidef (S : Matrix (Fin m) (Fin n) ℂ) :
    (amplitudeDensity S).PosSemidef :=
  posSemidef_vecMulVec_self_star _

/-- The transpose in row-first vectorization fixes the marginal orientation. -/
theorem partialTrace_amplitudeDensity (S : Matrix (Fin m) (Fin n) ℂ) :
    partialTraceSecondOp (amplitudeDensity S) = S * Sᴴ := by
  ext i k
  rfl

theorem trace_amplitudeDensity (S : Matrix (Fin m) (Fin n) ℂ) :
    trace (amplitudeDensity S) = trace (S * Sᴴ) := by
  rw [← partialTraceSecondOp_trace (amplitudeDensity S), partialTrace_amplitudeDensity]

theorem amplitudeVector_norm_sq (S : Matrix (Fin m) (Fin n) ℂ) :
    ‖amplitudeVector S‖ ^ 2 = (trace (S * Sᴴ)).re := by
  rw [amplitudeVector, InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    EuclideanSpace.inner_toLp_toLp, ← trace_vecMulVec]
  exact congrArg Complex.re (trace_amplitudeDensity S)

theorem amplitudeVector_norm_eq_one (S : Matrix (Fin m) (Fin n) ℂ)
    (htrace : trace (S * Sᴴ) = 1) : ‖amplitudeVector S‖ = 1 := by
  have hsq : ‖amplitudeVector S‖ ^ 2 = 1 := by
    rw [amplitudeVector_norm_sq, htrace, Complex.one_re]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hsq)

/-- A normalized amplitude gives an idempotent positive outer-product operator. -/
theorem amplitudeDensity_idempotent (S : Matrix (Fin m) (Fin n) ℂ)
    (htrace : trace (S * Sᴴ) = 1) : IsIdempotentElem (amplitudeDensity S) := by
  have hv : star (vec Sᵀ) ⬝ᵥ vec Sᵀ = 1 := by
    rw [dotProduct_comm, ← trace_vecMulVec]
    exact (trace_amplitudeDensity S).trans htrace
  change vecMulVec (vec Sᵀ) (star (vec Sᵀ)) *
    vecMulVec (vec Sᵀ) (star (vec Sᵀ)) = _
  rw [vecMulVec_mul_vecMulVec, hv, one_smul]
  rfl

end Amplitudes

section PositiveStates

variable {n : ℕ}

/-- Native CFC gives an ordered Gram factorization of every positive matrix. -/
theorem sqrt_mul_conjTranspose {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) : CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ = ρ := by
  have hs := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  rw [hs.eq, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

theorem partialTrace_sqrt_purification {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) :
    partialTraceSecondOp (amplitudeDensity (CFC.sqrt ρ)) = ρ := by
  rw [partialTrace_amplitudeDensity, sqrt_mul_conjTranspose hρ]

theorem trace_sqrt_purification {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) : trace (amplitudeDensity (CFC.sqrt ρ)) = trace ρ := by
  rw [trace_amplitudeDensity, sqrt_mul_conjTranspose hρ]

theorem sqrt_purification_idempotent {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (htrace : trace ρ = 1) :
    IsIdempotentElem (amplitudeDensity (CFC.sqrt ρ)) := by
  apply amplitudeDensity_idempotent
  rw [sqrt_mul_conjTranspose hρ, htrace]

theorem sqrt_purification_norm_eq_one {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (htrace : trace ρ = 1) :
    ‖amplitudeVector (CFC.sqrt ρ)‖ = 1 := by
  apply amplitudeVector_norm_eq_one
  rw [sqrt_mul_conjTranspose hρ, htrace]

end PositiveStates

section DoubledGenerator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The doubled action is exactly the ordered commutator on a full amplitude. -/
theorem doubledGenerator_action (H S : Matrix ι ι ℂ) :
    (H ⊗ₖ 1 - 1 ⊗ₖ Hᵀ) *ᵥ vec Sᵀ = vec (H * S - S * H)ᵀ := by
  simp only [sub_mulVec, kronecker_mulVec_vec, one_mul, mul_one,
    transpose_one, transpose_sub, transpose_mul, vec_sub]

theorem doubledGenerator_annihilates_of_commute (H S : Matrix ι ι ℂ)
    (h : Commute H S) : (H ⊗ₖ 1 - 1 ⊗ₖ Hᵀ) *ᵥ vec Sᵀ = 0 := by
  rw [doubledGenerator_action, h.eq, sub_self, transpose_zero, vec_zero]

end DoubledGenerator

section Gibbs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit trace normalization of the existing full-matrix CFC Gibbs weight. -/
def normalizedGibbs (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) : Matrix ι ι ℂ :=
  (trace (gibbsDensity H hH β))⁻¹ • gibbsDensity H hH β

theorem normalizedGibbs_posSemidef (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (normalizedGibbs H hH β).PosSemidef := by
  have hD := (gibbsDensity_nonneg H hH β).posSemidef
  exact hD.smul (inv_nonneg.mpr hD.trace_nonneg)

theorem trace_normalizedGibbs [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    trace (normalizedGibbs H hH β) = 1 := by
  rw [normalizedGibbs, trace_smul]
  exact inv_mul_cancel₀ (gibbsPartition_ne_zero H hH β)

/-- The normalized matrix represents the preexisting Gibbs functional exactly. -/
theorem normalizedGibbs_readout [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) (A : Matrix ι ι ℂ) :
    trace (normalizedGibbs H hH β * A) = gibbsFunctional H hH β A := by
  simp only [normalizedGibbs, smul_mul, trace_smul, gibbsFunctional_apply, smul_eq_mul]

theorem normalizedGibbs_commute (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Commute (normalizedGibbs H hH β) H := by
  have hD : Commute (gibbsDensity H hH β) H := by
    change Commute (hH.cfc (expWeight β)) H
    rw [← hH.cfc_eq]
    have hsa : IsSelfAdjoint H := hH
    exact hsa.commute_cfc (Commute.refl H) (expWeight β)
  exact hD.smul_left _

/-- Commutation of the square-root amplitude is derived, not postulated. -/
theorem sqrt_normalizedGibbs_commute
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Commute (CFC.sqrt (normalizedGibbs H hH β)) H := by
  exact (normalizedGibbs_commute H hH β).cfcₙ_nnreal NNReal.sqrt

theorem doubledGenerator_gibbs_amplitude
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (H ⊗ₖ 1 - 1 ⊗ₖ Hᵀ) *ᵥ vec (CFC.sqrt (normalizedGibbs H hH β))ᵀ = 0 :=
  doubledGenerator_annihilates_of_commute H _ (sqrt_normalizedGibbs_commute H hH β).symm

end Gibbs

section GibbsPurification

variable {n : ℕ} [Nonempty (Fin n)]

/-- The full CFC Gibbs state admits a positive trace-one idempotent purification,
witnessed by the outer product of its native square-root amplitude. -/
theorem exists_gibbs_purification
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    ∃ P : BipartiteOperator n n,
      P.PosSemidef ∧ trace P = 1 ∧ IsIdempotentElem P ∧
        partialTraceSecondOp P = normalizedGibbs H hH β := by
  have hρ := normalizedGibbs_posSemidef H hH β
  have ht := trace_normalizedGibbs H hH β
  exact ⟨amplitudeDensity (CFC.sqrt (normalizedGibbs H hH β)),
    amplitudeDensity_posSemidef _, (trace_sqrt_purification hρ).trans ht,
    sqrt_purification_idempotent hρ ht, partialTrace_sqrt_purification hρ⟩

end GibbsPurification

end InfoGeometry.Quantum.MatrixBoundaryPurification
