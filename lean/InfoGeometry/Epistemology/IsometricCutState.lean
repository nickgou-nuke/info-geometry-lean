import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Star.Real
import InfoGeometry.Inference.FiniteGibbsThermodynamicIdentity

/-!
# Finite isometric cut states

A rectangular real isometry encodes a uniform finite cut state. The boundary
operator is a normalized orthogonal projection. No graph minimum or perfect
tensor contraction is assumed or asserted in this prerequisite module.
-/

noncomputable section
namespace InfoGeometry.Epistemology.IsometricCutState
open Matrix
open scoped BigOperators

variable {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

def cutProjection (W : Matrix B C ℝ) : Matrix B B ℝ := W * Wᵀ

def cutDensity (W : Matrix B C ℝ) : Matrix B B ℝ :=
  (Fintype.card C : ℝ)⁻¹ • cutProjection W

theorem cutProjection_sq (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    cutProjection W * cutProjection W = cutProjection W := by
  unfold cutProjection
  calc
    (W * Wᵀ) * (W * Wᵀ) = W * (Wᵀ * W) * Wᵀ := by simp only [Matrix.mul_assoc]
    _ = W * Wᵀ := by rw [hW]; simp

theorem cutProjection_posSemidef (W : Matrix B C ℝ) :
    (cutProjection W).PosSemidef := by
  simpa [cutProjection] using Matrix.posSemidef_self_mul_conjTranspose W

theorem cutDensity_posSemidef (W : Matrix B C ℝ) :
    (cutDensity W).PosSemidef :=
  (cutProjection_posSemidef W).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem cutProjection_trace (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    Matrix.trace (cutProjection W) = Fintype.card C := by
  unfold cutProjection
  rw [Matrix.trace_mul_comm, hW]
  simp

theorem cutDensity_trace [Nonempty C] (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    Matrix.trace (cutDensity W) = 1 := by
  rw [cutDensity, Matrix.trace_smul, cutProjection_trace W hW]
  have hn : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [smul_eq_mul] using inv_mul_cancel₀ hn

theorem cutDensity_sq (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    cutDensity W * cutDensity W = (Fintype.card C : ℝ)⁻¹ • cutDensity W := by
  simp only [cutDensity, Matrix.smul_mul, Matrix.mul_smul, cutProjection_sq W hW]

/-- The encoding columns span the nonzero-eigenvalue sector. -/
theorem cutDensity_mul_encoding (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    cutDensity W * W = (Fintype.card C : ℝ)⁻¹ • W := by
  rw [cutDensity, cutProjection, Matrix.smul_mul, Matrix.mul_assoc, hW, Matrix.mul_one]

/-- The isometry's columns are independent. -/
theorem encoding_injective (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    Function.Injective (fun x : C → ℝ => W *ᵥ x) := by
  intro x y h
  have hp := congrArg (fun z => Wᵀ *ᵥ z) h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW] at hp
  simpa using hp

/-- The support projection has exactly the cut dimension. -/
theorem cutProjection_rank (W : Matrix B C ℝ) (hW : Wᵀ * W = 1) :
    (cutProjection W).rank = Fintype.card C := by
  have hgram : (Wᵀ * W).rank = W.rank := by
    simpa using Matrix.rank_conjTranspose_mul_self W
  have hrank : W.rank = Fintype.card C := by
    rw [hW] at hgram
    simpa using hgram.symm
  calc
    (cutProjection W).rank = W.rank := by
      simpa [cutProjection] using Matrix.rank_self_mul_conjTranspose W
    _ = Fintype.card C := hrank

def uniformCutWeight (C : Type*) [Fintype C] : C → ℝ :=
  fun _ => 1 / (Fintype.card C : ℝ)

theorem uniformCutWeight_pos [Nonempty C] (i : C) : 0 < uniformCutWeight C i := by
  unfold uniformCutWeight
  have hn : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  exact div_pos zero_lt_one hn

theorem uniformCutWeight_sum [Nonempty C] : ∑ i, uniformCutWeight C i = 1 := by
  simp only [uniformCutWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The entropy is computed from an actual normalized finite weight vector. -/
theorem uniformCutWeight_entropy [Nonempty C] :
    InfoGeometry.Inference.FiniteGibbs.entropyOf (uniformCutWeight C) =
      Real.log (Fintype.card C) := by
  apply (InfoGeometry.Inference.FiniteGibbs.entropyOf_eq_log_card_iff_uniform
    (uniformCutWeight C) uniformCutWeight_pos uniformCutWeight_sum).mpr
  intro i
  rfl

/-- Tensor-product cardinality turns the computed uniform entropy into the
bond capacity; no entropy equality is assumed. -/
theorem uniformCutWeight_entropy_capacity [Nonempty C] (chi k : ℕ)
    (hcard : Fintype.card C = chi ^ k) :
    InfoGeometry.Inference.FiniteGibbs.entropyOf (uniformCutWeight C) =
      (k : ℝ) * Real.log (chi : ℝ) := by
  rw [uniformCutWeight_entropy, hcard, Nat.cast_pow, Real.log_pow]

end InfoGeometry.Epistemology.IsometricCutState
