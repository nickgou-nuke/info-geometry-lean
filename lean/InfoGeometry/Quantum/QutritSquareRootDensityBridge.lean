import InfoGeometry.Probability.SquareRootSimplexBridge
import InfoGeometry.Quantum.QutritDensityMatrix

/-!
# Qutrit probability and square-root coordinates

This file connects two existing finite owners without identifying their
carriers: `computationalProbability` supplies the normalized qutrit
probability vector, while `squareRootEmbedding` supplies its radius-two
square-root coordinates.  The diagonal density-matrix readout remains owned
by `QutritDensityMatrix`.
-/

open scoped BigOperators

namespace InfoGeometry.Quantum.Qutrit

open InfoGeometry.Probability.Homological
open InfoGeometry.Probability.SquareRootSimplexBridge

theorem qutrit_squareRootEmbedding_sum_sq (ψ : QutritState) :
    ∑ i, (squareRootEmbedding 3 (computationalProbability ψ) i) ^ 2 = 4 := by
  exact squareRootEmbedding_sum_sq
    (computationalProbability ψ)
    (fun i => computationalProbability_nonneg ψ i)
    (sum_computationalProbability ψ)

theorem pureDensityMatrix_diagonal_eq_squareRoot_sq_div_four
    (ψ : QutritState) (i : Fin 3) :
    pureDensityMatrix ψ i i =
      (((squareRootEmbedding 3 (computationalProbability ψ) i) ^ 2 / 4 : ℝ) : ℂ) := by
  rw [pureDensityMatrix_diagonal]
  rw [squareRootEmbedding_sq (computationalProbability ψ)
    (fun j => computationalProbability_nonneg ψ j) i]
  norm_num

theorem pureDensityMatrix_posSemidef (ψ : QutritState) :
    Matrix.PosSemidef (pureDensityMatrix ψ) := by
  simpa [pureDensityMatrix, Matrix.vecMulVec_apply] using
    (Matrix.posSemidef_vecMulVec_self_star (ψ : QutritSpace))

theorem pureDensityMatrix_globalPhaseAct_invariant
    (δ : ℝ) (ψ : QutritState) :
    pureDensityMatrix (globalPhaseAct δ ψ) = pureDensityMatrix ψ := by
  have hphase : conj (phase δ) * phase δ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phase]
    norm_num
  ext i j
  change
    (matrixOp (globalPhaseMatrix δ) (ψ : QutritSpace)) i *
        conj ((matrixOp (globalPhaseMatrix δ) (ψ : QutritSpace)) j) =
      (ψ : QutritSpace) i * conj ((ψ : QutritSpace) j)
  rw [globalPhaseMatrix_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (phase δ * (ψ : QutritSpace) i) *
        conj (phase δ * (ψ : QutritSpace) j) =
        (conj (phase δ) * phase δ) *
          ((ψ : QutritSpace) i * conj ((ψ : QutritSpace) j)) := by
            simp only [map_mul]
            ring
    _ = (ψ : QutritSpace) i * conj ((ψ : QutritSpace) j) := by
      rw [hphase]
      simp

theorem qutrit_squareRootEmbedding_globalPhase_invariant
    (δ : ℝ) (ψ : QutritState) :
    squareRootEmbedding 3 (computationalProbability (globalPhaseAct δ ψ)) =
      squareRootEmbedding 3 (computationalProbability ψ) := by
  funext i
  rw [computationalProbability_globalPhaseAct δ ψ i]

end InfoGeometry.Quantum.Qutrit
