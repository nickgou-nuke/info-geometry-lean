import InfoGeometry.Canonical.FiniteWeylStarProduct
import InfoGeometry.Canonical.CantorGibbsPoUBridge

/-!
# Finite Weyl-symbol readout of positive Gr(2,4) channels

This bridge places the six normalized positive Plücker-channel weights on the
six diagonal states of the existing six-state operator carrier, then transports
the resulting operator through the verified Stokes--Weyl symbol equivalence.
The transported finite star product therefore reads back as the pointwise
product of diagonal channel weights. This is a finite symbol/operator result;
it does not claim a smooth super-Grassmannian Moyal formula.
-/

noncomputable section

namespace InfoGeometry.Canonical.Gr24FiniteWeylSymbolBridge

open scoped BigOperators
open InfoGeometry.Canonical.FiniteWeylStarProduct
open InfoGeometry.Canonical.CantorGibbsPoUBridge
open InfoGeometry.Canonical.CantorPlabicTwistorBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

abbrev Gr24MatrixIndex := Fin 2 × Fin 3
abbrev Gr24Matrix := Matrix Gr24MatrixIndex Gr24MatrixIndex ℂ

/-- Encode the six Plücker channels in row-major order on the six matrix
coordinates `Fin 2 × Fin 3`. -/
def channelToMatrixIndex (i : Fin 6) : Gr24MatrixIndex :=
  ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩⟩

def matrixIndexToChannel (p : Gr24MatrixIndex) : Fin 6 :=
  ⟨p.1.val * 3 + p.2.val, by omega⟩

theorem matrixIndexToChannel_channelToMatrixIndex (i : Fin 6) :
    matrixIndexToChannel (channelToMatrixIndex i) = i := by
  apply Fin.ext
  simp only [matrixIndexToChannel, channelToMatrixIndex]
  omega

theorem channelToMatrixIndex_matrixIndexToChannel (p : Gr24MatrixIndex) :
    channelToMatrixIndex (matrixIndexToChannel p) = p := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [channelToMatrixIndex, matrixIndexToChannel] <;> omega

/-- The diagonal density operator whose diagonal entries are the normalized
squared Plücker coordinates. -/
def pluckerDensityOperator (M : Matrix2x4) : Gr24Matrix :=
  Matrix.diagonal fun p =>
    (pluckerSectorProbability M (matrixIndexToChannel p) : ℂ)

/-- The Weyl symbol of the positive-Grassmannian channel density. -/
def pluckerWeylSymbol (M : Matrix2x4) : WeylSymbol6 :=
  symbolToOperator.symm (pluckerDensityOperator M)

theorem pluckerWeylSymbol_operator (M : Matrix2x4) :
    symbolToOperator (pluckerWeylSymbol M) = pluckerDensityOperator M := by
  simp [pluckerWeylSymbol]

@[simp] theorem pluckerDensityOperator_apply (M : Matrix2x4)
    (p : Gr24MatrixIndex) :
    pluckerDensityOperator M p p =
      (pluckerSectorProbability M (matrixIndexToChannel p) : ℂ) := by
  simp [pluckerDensityOperator]

theorem pluckerDensityOperator_offDiagonal (M : Matrix2x4)
    {p q : Gr24MatrixIndex} (hpq : p ≠ q) :
    pluckerDensityOperator M p q = 0 := by
  simp [pluckerDensityOperator, hpq]

theorem diagonal_mul_diagonal {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α → ℂ) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal (fun i => a i * b i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, hij]

/-- The finite Weyl product of two Plücker density symbols is the diagonal
operator with pointwise-multiplied channel weights. -/
theorem pluckerWeylStar_operator (M N : Matrix2x4) :
    symbolToOperator (finiteWeylStar (pluckerWeylSymbol M)
      (pluckerWeylSymbol N)) =
      Matrix.diagonal (fun p =>
        ((pluckerSectorProbability M (matrixIndexToChannel p) : ℝ) : ℂ) *
        ((pluckerSectorProbability N (matrixIndexToChannel p) : ℝ) : ℂ)) := by
  rw [symbolToOperator_finiteWeylStar,
    pluckerWeylSymbol_operator, pluckerWeylSymbol_operator]
  simp only [pluckerDensityOperator]
  exact diagonal_mul_diagonal _ _

theorem pluckerWeylStar_channel_readout (M N : Matrix2x4)
    (i : Fin 6) :
    symbolToOperator (finiteWeylStar (pluckerWeylSymbol M)
      (pluckerWeylSymbol N)) (channelToMatrixIndex i) (channelToMatrixIndex i) =
      ((pluckerSectorProbability M i : ℝ) : ℂ) *
        ((pluckerSectorProbability N i : ℝ) : ℂ) := by
  rw [pluckerWeylStar_operator]
  simp [matrixIndexToChannel_channelToMatrixIndex]

/-- The existing Gibbs-PoU reconstruction is preserved after Weyl-symbol
encoding: its diagonal symbol readout is exactly the positive Plücker law. -/
theorem gibbsPoU_weylSymbol_readout (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (ε : ℝ) (hε : 0 < ε) (i : Fin 6) :
    symbolToOperator (pluckerWeylSymbol M)
      (channelToMatrixIndex i) (channelToMatrixIndex i) =
      ((pluckerSectorGibbsPoU M hM ε).weight i : ℂ) := by
  rw [pluckerWeylSymbol_operator]
  rw [pluckerDensityOperator_apply]
  rw [pluckerSectorGibbsPoU_eq_born M hM ε hε]
  simp [pluckerSectorBornFinitePoU, matrixIndexToChannel_channelToMatrixIndex]

end InfoGeometry.Canonical.Gr24FiniteWeylSymbolBridge

end noncomputable section
