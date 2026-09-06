import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Krein.LaggedCoincidenceDiracOperator

/-!
# Finite Sinkhorn gauge invariants

This owner packages the finite algebraic invariants of a positive two-sided
diagonal scaling.  It does not assert existence or convergence of a Sinkhorn
iteration.  The scaling is supplied explicitly, while row/column
normalization and bistochastic certificates remain owned by `SinkhornFoundation`.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.SinkhornGaugeInvariantMatrixBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Krein

variable {n : ℕ}

abbrev GaugeMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-! ## Two-sided diagonal gauge -/

noncomputable def twoSidedDiagonalGauge
    (a b : Fin n → ℝ) (M : GaugeMatrix n) : GaugeMatrix n :=
  Matrix.diagonal a * M * Matrix.diagonal b

@[simp] theorem twoSidedDiagonalGauge_apply
    (a b : Fin n → ℝ) (M : GaugeMatrix n) (i j : Fin n) :
    twoSidedDiagonalGauge a b M i j = a i * M i j * b j := by
  simp [twoSidedDiagonalGauge, Matrix.mul_apply, Matrix.diagonal]

theorem sinkhornTwoStep_eq_twoSidedDiagonalGauge
    (M : GaugeMatrix n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol =
      twoSidedDiagonalGauge
        (leftWeylScale n M)
        (rightWeylScale n (rowNormalize n M hrow)) M := by
  exact sinkhornTwoStep_eq_weylGauge (n := n) M hrow hcol

/-! ## Cross-ratio invariance -/

noncomputable def matrixCrossRatio
    (M : GaugeMatrix n) (i k j l : Fin n) : ℝ :=
  (M i j * M k l) / (M i l * M k j)

theorem matrixCrossRatio_twoSidedDiagonalGauge
    (a b : Fin n → ℝ) (M : GaugeMatrix n) (i k j l : Fin n)
    (ha : ∀ r, a r ≠ 0) (hb : ∀ r, b r ≠ 0)
    (hM : M i j ≠ 0 ∧ M k l ≠ 0 ∧ M i l ≠ 0 ∧ M k j ≠ 0) :
    matrixCrossRatio (twoSidedDiagonalGauge a b M) i k j l =
      matrixCrossRatio M i k j l := by
  rcases hM with ⟨hij, hkl, hil, hkj⟩
  unfold matrixCrossRatio
  rw [twoSidedDiagonalGauge_apply, twoSidedDiagonalGauge_apply,
    twoSidedDiagonalGauge_apply, twoSidedDiagonalGauge_apply]
  field_simp [ha i, ha k, hb j, hb l, hij, hkl, hil, hkj]

/-! ## Log-affinity and triangle holonomy -/

noncomputable def directedLogAffinity
    (M : GaugeMatrix n) (i j : Fin n) : ℝ :=
  Real.log (M i j / M j i)

noncomputable def diagonalGaugePotential
    (a b : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.log (a i) - Real.log (b i)

theorem directedLogAffinity_twoSidedDiagonalGauge
    (a b : Fin n → ℝ) (M : GaugeMatrix n) (i j : Fin n)
    (ha : ∀ r, 0 < a r) (hb : ∀ r, 0 < b r)
    (hM : ∀ r s, 0 < M r s) :
    directedLogAffinity (twoSidedDiagonalGauge a b M) i j =
      directedLogAffinity M i j +
        diagonalGaugePotential a b i - diagonalGaugePotential a b j := by
  unfold directedLogAffinity diagonalGaugePotential
  rw [twoSidedDiagonalGauge_apply, twoSidedDiagonalGauge_apply]
  calc
    Real.log ((a i * M i j * b j) / (a j * M j i * b i)) =
        Real.log (a i * M i j * b j) -
          Real.log (a j * M j i * b i) := by
      rw [Real.log_div]
      · exact (mul_pos (mul_pos (ha i) (hM i j)) (hb j)).ne'
      · exact (mul_pos (mul_pos (ha j) (hM j i)) (hb i)).ne'
    _ = (Real.log (a i) + Real.log (M i j) + Real.log (b j)) -
          (Real.log (a j) + Real.log (M j i) + Real.log (b i)) := by
      rw [Real.log_mul (mul_pos (ha i) (hM i j)).ne' (hb j).ne',
        Real.log_mul (ha i).ne' (hM i j).ne',
        Real.log_mul (mul_pos (ha j) (hM j i)).ne' (hb i).ne',
        Real.log_mul (ha j).ne' (hM j i).ne']
    _ = Real.log (M i j / M j i) +
          (Real.log (a i) - Real.log (b i)) -
            (Real.log (a j) - Real.log (b j)) := by
      rw [Real.log_div]
      · ring
      · exact (hM i j).ne'
      · exact (hM j i).ne'

noncomputable def triangleLogHolonomy
    (M : GaugeMatrix n) (i j k : Fin n) : ℝ :=
  directedLogAffinity M i j + directedLogAffinity M j k +
    directedLogAffinity M k i

theorem triangleLogHolonomy_twoSidedDiagonalGauge
    (a b : Fin n → ℝ) (M : GaugeMatrix n) (i j k : Fin n)
    (ha : ∀ r, 0 < a r) (hb : ∀ r, 0 < b r)
    (hM : ∀ r s, 0 < M r s) :
    triangleLogHolonomy (twoSidedDiagonalGauge a b M) i j k =
      triangleLogHolonomy M i j k := by
  simp only [triangleLogHolonomy]
  rw [directedLogAffinity_twoSidedDiagonalGauge a b M i j ha hb hM,
    directedLogAffinity_twoSidedDiagonalGauge a b M j k ha hb hM,
    directedLogAffinity_twoSidedDiagonalGauge a b M k i ha hb hM]
  ring

/-! ## Doubled coincidence operator -/

noncomputable def doubledDiagonalGauge
    (a b : Fin n → ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal a) 0 0 (Matrix.diagonal b)

theorem laggedCoincidenceDirac_twoSidedDiagonalGauge
    (a b : Fin n → ℝ) (M : GaugeMatrix n) :
    laggedCoincidenceDirac (twoSidedDiagonalGauge a b M) =
      doubledDiagonalGauge a b * laggedCoincidenceDirac M *
        doubledDiagonalGauge a b := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [laggedCoincidenceDirac, twoSidedDiagonalGauge,
      doubledDiagonalGauge, Matrix.fromBlocks, Matrix.mul_apply,
      Matrix.diagonal] <;> ring

theorem laggedCoincidenceDirac_twoSidedDiagonalGauge_square
    (a b : Fin n → ℝ) (M : GaugeMatrix n) :
    laggedCoincidenceDirac (twoSidedDiagonalGauge a b M) *
        laggedCoincidenceDirac (twoSidedDiagonalGauge a b M) =
      Matrix.fromBlocks
        (twoSidedDiagonalGauge a b M *
          (twoSidedDiagonalGauge a b M).transpose) 0 0
        ((twoSidedDiagonalGauge a b M).transpose *
          twoSidedDiagonalGauge a b M) := by
  exact laggedCoincidenceDirac_square (twoSidedDiagonalGauge a b M)

end InfoGeometry.Canonical.SinkhornGaugeInvariantMatrixBridge
