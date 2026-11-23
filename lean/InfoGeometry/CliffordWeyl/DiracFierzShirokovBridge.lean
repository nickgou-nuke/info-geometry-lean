/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracBilinearChannels
import InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
import InfoGeometry.Synthesis.ShirokovRecursiveInverse
import InfoGeometry.Synthesis.FierzShirokovCoefficientBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Dirac-adjoint Fierz dyads and Shirokov scalar-part recurrence

The owner `DiracBilinearChannels` reconstructs the Dirac-adjoint rank-one
operator from its sixteen trace-dual bilinear coordinates.  This file feeds
that same finite `4 × 4` operator into the existing Shirokov recurrence with
normalized trace `trace / 4`.  It proves the resulting coefficient sequence
for a rank-one dyad.  The statement is confined to the explicit matrix
representation and does not promote the generic recurrence definition to a
general Clifford-algebra correctness theorem.
-/

noncomputable section

namespace InfoGeometry.CliffordWeyl.DiracFierzShirokovBridge

open InfoGeometry.Clifford.CrawfordDiracBispinorDensities
open InfoGeometry.CliffordWeyl.DiracBilinearChannels
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open InfoGeometry.Synthesis.ShirokovRecursiveInverse
open InfoGeometry.Synthesis.FierzShirokovCoefficientBridge

/-- The normalized scalar-part readout on the concrete complex Dirac matrix
carrier, represented as a linear map so the generic Shirokov recurrence
theorems apply directly. -/
def diracScalarPart : DiracMatrix →ₗ[ℂ] ℂ :=
  (4 : ℂ)⁻¹ • Matrix.traceLinearMap (Fin 4) ℂ ℂ

/-- The Dirac-adjoint scalar pairing `bar left * right`, represented by the
existing matrix metric bilinear. -/
def diracScalarPairing (left right : DiracSpinor) : ℂ :=
  InfoGeometry.CliffordWeyl.SpinorBilinearSoldering.bilinear gamma0 1 left right

private theorem diracDyad_eq_solder (left right : DiracSpinor) :
    diracDyad left right = solder gamma0 right left := rfl

private theorem diracDyad_trace (left right : DiracSpinor) :
    Matrix.trace (diracDyad left right) = diracScalarPairing left right := by
  have h := solder_trace_readout gamma0 (1 : DiracMatrix) right left
  simpa [diracScalarPairing, diracDyad_eq_solder, solder] using h

/-- The characteristic polynomial of the concrete Dirac-adjoint dyad is
`X^3 * (X - s)`, where `s = bar(left) * right`.  This spectral invariant
records the scalar eigenvalue and characteristic multiplicities, but does not
determine the dyad: when `s = 0`, a nonzero nilpotent dyad can remain. -/
theorem diracDyad_charpoly (left right : DiracSpinor) :
    (diracDyad left right).charpoly =
      Polynomial.X ^ 4 - Polynomial.C (diracScalarPairing left right) *
        Polynomial.X ^ 3 := by
  have hdot : right ⬝ᵥ Matrix.vecMul (star left) gamma0 =
      diracScalarPairing left right := by
    calc
      right ⬝ᵥ Matrix.vecMul (star left) gamma0 =
          Matrix.trace (diracDyad left right) := by
            simp [diracDyad, Matrix.trace_vecMulVec]
      _ = diracScalarPairing left right := diracDyad_trace left right
  rw [diracDyad, Matrix.charpoly_vecMulVec, hdot]
  norm_num [Fintype.card_fin, Polynomial.smul_eq_C_mul]

/-- Factored form of the rank-one characteristic polynomial. -/
theorem diracDyad_charpoly_factor (left right : DiracSpinor) :
    (diracDyad left right).charpoly = Polynomial.X ^ 3 *
      (Polynomial.X - Polynomial.C (diracScalarPairing left right)) := by
  rw [diracDyad_charpoly]
  ring

private theorem diracDyad_square (left right : DiracSpinor) :
    diracDyad left right * diracDyad left right =
      diracScalarPairing left right • diracDyad left right := by
  simpa [diracScalarPairing, diracDyad_eq_solder, solder,
    InfoGeometry.CliffordWeyl.SpinorBilinearSoldering.bilinear] using
    solder_fierz_product gamma0 right left right left

private theorem diracDyad_scalarPart (left right : DiracSpinor) :
    diracScalarPart (diracDyad left right) =
      diracScalarPairing left right / (4 : ℂ) := by
  simp [diracScalarPart, diracDyad_trace, div_eq_mul_inv, mul_comm]

private theorem diracShirokovC_zero (k : ℕ) :
    shirokovC diracScalarPart 4 (0 : DiracMatrix) k = 0 := by
  cases k with
  | zero => simp [shirokovC_zero, diracScalarPart]
  | succ k => simp [shirokovC_succ, diracScalarPart]

/-- The first Shirokov coefficient is the Dirac scalar bilinear. -/
theorem diracDyad_shirokov_c_one (left right : DiracSpinor) :
    shirokovC diracScalarPart 4 (diracDyad left right) 0 =
      diracScalarPairing left right := by
  exact shirokovC_one_of_readout diracScalarPart 4 (by norm_num)
    (diracDyad left right) (diracScalarPairing left right)
    (diracDyad_scalarPart left right)

/-- The degree-four Shirokov sequence for a Dirac-adjoint rank-one dyad:
`C₁ = bar(left) right`, and `U₂,C₂,U₃,C₃,U₄,C₄` all vanish.  Thus the
characteristic data retain only the scalar eigenvalue; when that scalar is
zero, the dyad can still be nonzero and nilpotent. -/
theorem diracDyad_shirokov_rank_one_sequence (left right : DiracSpinor) :
    shirokovC diracScalarPart 4 (diracDyad left right) 0 =
        diracScalarPairing left right ∧
      shirokovU diracScalarPart 4 (diracDyad left right) 1 = 0 ∧
      shirokovC diracScalarPart 4 (diracDyad left right) 1 = 0 ∧
      shirokovU diracScalarPart 4 (diracDyad left right) 2 = 0 ∧
      shirokovC diracScalarPart 4 (diracDyad left right) 2 = 0 ∧
      shirokovU diracScalarPart 4 (diracDyad left right) 3 = 0 ∧
      shirokovC diracScalarPart 4 (diracDyad left right) 3 = 0 := by
  have hc₁ := diracDyad_shirokov_c_one left right
  have hφ := diracDyad_scalarPart left right
  have ha2 : diracDyad left right * diracDyad left right =
      algebraMap ℂ DiracMatrix (diracScalarPairing left right) *
        diracDyad left right := by
    simpa [Algebra.smul_def] using diracDyad_square left right
  have hU := shirokovU_eq_zero_of_one_le diracScalarPart 4 (by norm_num)
    (diracDyad left right) (diracScalarPairing left right) hφ ha2
  have hc₂ := shirokovC_eq_zero_of_u_succ_eq_zero diracScalarPart 4
    (diracDyad left right) 0 (hU 1 (by omega))
  have hc₃ := shirokovC_eq_zero_of_u_succ_eq_zero diracScalarPart 4
    (diracDyad left right) 1 (hU 2 (by omega))
  have hc₄ := shirokovC_eq_zero_of_u_succ_eq_zero diracScalarPart 4
    (diracDyad left right) 2 (hU 3 (by omega))
  exact ⟨hc₁, hU 1 (by omega), hc₂, hU 2 (by omega), hc₃,
    hU 3 (by omega), hc₄⟩

/-- Beyond the displayed four-dimensional characteristic readout, every
later finite Shirokov coefficient of the rank-one Dirac dyad also vanishes. -/
theorem diracDyad_shirokov_coefficients_zero_after_first
    (left right : DiracSpinor) :
    ∀ k : ℕ, 1 ≤ k →
      shirokovC diracScalarPart 4 (diracDyad left right) k = 0 := by
  exact shirokovC_eq_zero_of_one_le diracScalarPart 4 (by norm_num)
    (diracDyad left right) (diracScalarPairing left right)
    (diracDyad_scalarPart left right)
    (by simpa [Algebra.smul_def] using diracDyad_square left right)

/-- Zero scalar pairing does not imply a zero Fierz aggregate: a concrete
Weyl-basis spinor produces a nonzero square-zero Dirac dyad. -/
theorem exists_nonzero_nilpotent_diracDyad_with_zero_scalar :
    ∃ spinor : DiracSpinor,
      diracScalarPairing spinor spinor = 0 ∧
      diracDyad spinor spinor ≠ 0 ∧
      diracDyad spinor spinor * diracDyad spinor spinor = 0 := by
  let spinor : DiracSpinor := ![1, 0, 0, 0]
  have hpair : diracScalarPairing spinor spinor = 0 := by
    norm_num [spinor, diracScalarPairing,
      InfoGeometry.CliffordWeyl.SpinorBilinearSoldering.bilinear, gamma0,
      InfoGeometry.CliffordWeyl.SpinorBilinearSoldering.diracRow,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  have hentry : diracDyad spinor spinor 0 2 = 1 := by
    norm_num [spinor, diracDyad, gamma0, Matrix.vecMulVec,
      Matrix.vecMul, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
  have hnonzero : diracDyad spinor spinor ≠ 0 := by
    intro h
    have := congrArg (fun M : DiracMatrix => M 0 2) h
    norm_num [hentry] at this
  refine ⟨spinor, hpair, hnonzero, ?_⟩
  rw [diracDyad_square, hpair, zero_smul]

/-- A concrete nonzero nilpotent Dirac dyad has characteristic polynomial
`X^4`; thus the zero characteristic coefficients do not imply that the
operator itself vanishes. -/
theorem exists_nonzero_nilpotent_diracDyad_with_charpoly_X_four :
    ∃ spinor : DiracSpinor,
      diracDyad spinor spinor ≠ 0 ∧
      diracDyad spinor spinor * diracDyad spinor spinor = 0 ∧
      (diracDyad spinor spinor).charpoly = Polynomial.X ^ 4 := by
  rcases exists_nonzero_nilpotent_diracDyad_with_zero_scalar with
    ⟨spinor, hscalar, hnonzero, hnilpotent⟩
  refine ⟨spinor, hnonzero, hnilpotent, ?_⟩
  rw [diracDyad_charpoly, hscalar]
  simp

/-- The degree-four Shirokov coefficient readout is not injective on Dirac
dyads: a nonzero square-zero dyad and the zero operator have the same four
coefficients when the Dirac scalar pairing vanishes. -/
theorem shirokov_coefficients_not_injective_on_dirac_dyads :
    ∃ spinor : DiracSpinor,
      diracDyad spinor spinor ≠ 0 ∧
      ∀ k : Fin 4,
        shirokovC diracScalarPart 4 (diracDyad spinor spinor) k.val =
          shirokovC diracScalarPart 4 (0 : DiracMatrix) k.val := by
  rcases exists_nonzero_nilpotent_diracDyad_with_zero_scalar with
    ⟨spinor, hscalar, hnonzero, _⟩
  rcases diracDyad_shirokov_rank_one_sequence spinor spinor with
    ⟨hc₁, _, hc₂, _, hc₃, _, hc₄⟩
  refine ⟨spinor, hnonzero, ?_⟩
  intro k
  fin_cases k
  · rw [hc₁, hscalar, diracShirokovC_zero]
  · rw [hc₂, diracShirokovC_zero]
  · rw [hc₃, diracShirokovC_zero]
  · rw [hc₄, diracShirokovC_zero]

/-- If a Dirac dyad is nonzero, at least one of its trace-dual Fierz channel
coordinates is nonzero.  This uses completeness, not Shirokov's four spectral
coefficients. -/
theorem exists_nonzero_fierz_channel_of_diracDyad_ne_zero
    (left right : DiracSpinor) (hDyad : diracDyad left right ≠ 0) :
    ∃ index : Fin 16,
      bilinear left (indexedChannel index).conjTranspose right ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hcoeff : channelCoefficient (diracDyad left right) =
      channelCoefficient (0 : DiracMatrix) := by
    funext index
    simp only [channelCoefficient]
    rw [trace_dyad_eq_bilinear, hnone index]
    simp
  have hzero := coefficients_injective hcoeff
  exact hDyad (by simpa using hzero)

end InfoGeometry.CliffordWeyl.DiracFierzShirokovBridge
