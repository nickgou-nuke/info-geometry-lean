import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Finite lagged-coincidence Gram and modular bridge

This file records only finite matrix identities.  It does not assert a polar
decomposition, matrix logarithm, or analytic modular-flow theorem.
-/

noncomputable section

namespace InfoGeometry.Krein.LaggedCoincidencePolarModularBridge

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

def rightGram (C : Matrix n n ℂ) : Matrix n n ℂ := Cᴴ * C

def leftGram (C : Matrix n n ℂ) : Matrix n n ℂ := C * Cᴴ

theorem rightGram_isHermitian (C : Matrix n n ℂ) :
    (rightGram C).IsHermitian := by
  exact isHermitian_conjTranspose_mul_self C

theorem leftGram_isHermitian (C : Matrix n n ℂ) :
    (leftGram C).IsHermitian := by
  exact isHermitian_mul_conjTranspose_self C

theorem rightGram_posSemidef (C : Matrix n n ℂ) :
    (rightGram C).PosSemidef := by
  exact posSemidef_conjTranspose_mul_self C

theorem leftGram_posSemidef (C : Matrix n n ℂ) :
    (leftGram C).PosSemidef := by
  exact posSemidef_self_mul_conjTranspose C

def laggedBlockDirac (C : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 0 Cᴴ C 0

@[simp] theorem laggedBlockDirac_isHermitian (C : Matrix n n ℂ) :
    (laggedBlockDirac C)ᴴ = laggedBlockDirac C := by
  dsimp [laggedBlockDirac]
  ext i j <;> cases i <;> cases j <;> simp [fromBlocks]

@[simp] theorem laggedBlockDirac_sq (C : Matrix n n ℂ) :
    laggedBlockDirac C * laggedBlockDirac C =
      fromBlocks (rightGram C) 0 0 (leftGram C) := by
  dsimp [laggedBlockDirac, rightGram, leftGram]
  rw [fromBlocks_multiply]
  simp

theorem trace_leftGram_eq_trace_rightGram (C : Matrix n n ℂ) :
    trace (leftGram C) = trace (rightGram C) := by
  dsimp [leftGram, rightGram]
  exact trace_mul_comm C Cᴴ

def gramTrace (C : Matrix n n ℂ) : ℂ := trace (rightGram C)

theorem gramTrace_formula (C : Matrix n n ℂ) :
    gramTrace C = (∑ i : n, ∑ j : n, Complex.normSq (C j i) : ℝ) := by
  apply Complex.ext
  · simp [gramTrace, rightGram, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose, Complex.normSq_apply]
  · simp [gramTrace, rightGram, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose, Complex.normSq_apply]
    ring_nf
    simp

theorem gramTrace_ne_zero_of_ne_zero {C : Matrix n n ℂ} (hC : C ≠ 0) :
    gramTrace C ≠ 0 := by
  intro hzero
  have hsum : ∑ i : n, ∑ j : n, Complex.normSq (C j i) = 0 := by
    have hreal := congrArg Complex.re (gramTrace_formula C)
    simpa [hzero] using hreal.symm
  have hrows :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i => Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _)).mp hsum
  apply hC
  funext i j
  have hrow : (∑ k : n, Complex.normSq (C k j)) = 0 := congrFun hrows j
  exact Complex.normSq_eq_zero.mp
    (congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg
        (fun k => Complex.normSq_nonneg (C k j))).mp hrow) i)

theorem gramTrace_eq_left_trace (C : Matrix n n ℂ) :
    gramTrace C = trace (leftGram C) :=
  (trace_leftGram_eq_trace_rightGram C).symm

def normalizedRightGram (C : Matrix n n ℂ) : Matrix n n ℂ :=
  (gramTrace C)⁻¹ • rightGram C

def normalizedLeftGram (C : Matrix n n ℂ) : Matrix n n ℂ :=
  (gramTrace C)⁻¹ • leftGram C

theorem normalizedRightGram_posSemidef (C : Matrix n n ℂ) :
    (normalizedRightGram C).PosSemidef := by
  apply Matrix.PosSemidef.smul (rightGram_posSemidef C)
  apply inv_nonneg.mpr
  rw [gramTrace_formula C]
  exact_mod_cast
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (C j i))

theorem normalizedLeftGram_posSemidef (C : Matrix n n ℂ) :
    (normalizedLeftGram C).PosSemidef := by
  apply Matrix.PosSemidef.smul (leftGram_posSemidef C)
  apply inv_nonneg.mpr
  rw [gramTrace_formula C]
  exact_mod_cast
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (C j i))

theorem trace_normalizedRightGram (C : Matrix n n ℂ) (hT : gramTrace C ≠ 0) :
    trace (normalizedRightGram C) = 1 := by
  dsimp [normalizedRightGram]
  rw [trace_smul, smul_eq_mul]
  change (gramTrace C)⁻¹ * gramTrace C = 1
  exact inv_mul_cancel₀ hT

theorem trace_normalizedLeftGram (C : Matrix n n ℂ) (hT : gramTrace C ≠ 0) :
    trace (normalizedLeftGram C) = 1 := by
  dsimp [normalizedLeftGram]
  rw [trace_smul, smul_eq_mul, ← gramTrace_eq_left_trace]
  exact inv_mul_cancel₀ hT

def sourceTargetGrading : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 0 0 (-1)

@[simp] theorem sourceTargetGrading_sq :
    sourceTargetGrading (n := n) * sourceTargetGrading = 1 := by
  dsimp [sourceTargetGrading]
  rw [fromBlocks_multiply]
  simp

def polarSign (U : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 0 Uᴴ U 0

theorem polarSign_sq (U : Matrix n n ℂ) (h₁ : U * Uᴴ = 1) (h₂ : Uᴴ * U = 1) :
    polarSign U * polarSign U = 1 := by
  dsimp [polarSign]
  rw [fromBlocks_multiply]
  simp [h₁, h₂]

theorem polarSign_anticommutes_grading (U : Matrix n n ℂ) :
    polarSign U * sourceTargetGrading =
      - (sourceTargetGrading * polarSign U) := by
  dsimp [polarSign, sourceTargetGrading]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  ext i j <;> cases i <;> cases j <;> simp [fromBlocks]

theorem leftGram_mul_affinity (C : Matrix n n ℂ) :
    leftGram C * C = C * rightGram C := by
  dsimp [leftGram, rightGram]
  exact Matrix.mul_assoc C Cᴴ C

theorem normalizedLeftGram_mul_affinity (C : Matrix n n ℂ) :
    normalizedLeftGram C * C = C * normalizedRightGram C := by
  dsimp [normalizedLeftGram, normalizedRightGram]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  rw [leftGram_mul_affinity]

def relativeGramModular (rhoL rhoRInv X : Matrix n n ℂ) : Matrix n n ℂ :=
  rhoL * X * rhoRInv

theorem relativeGramModular_affinity_eq_affinity (C rhoRInv : Matrix n n ℂ)
    (h_inv : normalizedRightGram C * rhoRInv = 1) :
    relativeGramModular (normalizedLeftGram C) rhoRInv C = C := by
  dsimp [relativeGramModular]
  rw [normalizedLeftGram_mul_affinity C]
  rw [Matrix.mul_assoc, h_inv, Matrix.mul_one]

end InfoGeometry.Krein.LaggedCoincidencePolarModularBridge
