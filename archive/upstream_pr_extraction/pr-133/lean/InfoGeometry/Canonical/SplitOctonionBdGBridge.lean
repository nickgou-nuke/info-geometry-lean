import InfoGeometry.Canonical.SplitOctonionThreeColorCausalMatrixRepresentation
import InfoGeometry.Canonical.SplitOctonionThreeColorDiracMatrixReadout
import InfoGeometry.Physics.BdGChiralBlockMatrix

/-!
# Split-octonion colour cores and BdG blocks

This owner supplies the canonical **linear** change of coordinates from one
associative colour core to `M₂(ℚ)`.  It deliberately does not introduce an
`AlgEquiv`: multiplicativity of the causal matrix readout is a separate
theorem obligation and is not inferred from a basis correspondence.
-/

namespace InfoGeometry.Physics.Bridge

open InfoGeometry.Canonical
open InfoGeometry.Physics
open Matrix

noncomputable section

variable (c : SplitOctonionColour)

def colorCoreToBdGLinear :
    colorCore c ≃ₗ[ℚ] BdGBlock ℚ :=
  threeColorCausalMatrixEquiv c

def bdgNPlus : BdGBlock ℚ := !![1, 0; 0, 0]
def bdgNMinus : BdGBlock ℚ := !![0, 0; 0, 1]
def bdgSigmaPlus : BdGBlock ℚ := !![0, 1; 0, 0]
def bdgSigmaMinus : BdGBlock ℚ := !![0, 0; 1, 0]

/-! The native two-sheet/Nambu operators.  These are ordinary matrices, not
Zorn matrices; the split-Cayley multiplication is a separate transported
product on the eight-dimensional carrier. -/

def bdgTau1 : BdGBlock ℚ := !![0, 1; 1, 0]
def bdgTau3 : BdGBlock ℚ := !![1, 0; 0, -1]
def bdgTauPlus : BdGBlock ℚ := bdgSigmaPlus
def bdgTauMinus : BdGBlock ℚ := bdgSigmaMinus
def bdgNullMetric : BdGBlock ℚ := bdgTau1
def bdgDiagonalMetric : BdGBlock ℚ := bdgTau3
def bdgHadamard : BdGBlock ℚ := !![1, 1; 1, -1]


@[simp] theorem colorCoreToBdGLinear_nPlus :
    colorCoreToBdGLinear c (colorPolarizedGenerator c 0) = bdgNPlus := by
  rw [colorCoreToBdGLinear, threeColorCausalMatrixEquiv_generator_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgNPlus, Matrix.stdBasis, threeColorMatrixIndexEquiv]

@[simp] theorem colorCoreToBdGLinear_nMinus :
    colorCoreToBdGLinear c (colorPolarizedGenerator c 1) = bdgNMinus := by
  rw [colorCoreToBdGLinear, threeColorCausalMatrixEquiv_generator_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgNMinus, Matrix.stdBasis, threeColorMatrixIndexEquiv]

@[simp] theorem colorCoreToBdGLinear_sigmaPlus :
    colorCoreToBdGLinear c (colorPolarizedGenerator c 2) = bdgSigmaPlus := by
  rw [colorCoreToBdGLinear, threeColorCausalMatrixEquiv_generator_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgSigmaPlus, Matrix.stdBasis, threeColorMatrixIndexEquiv]

@[simp] theorem colorCoreToBdGLinear_sigmaMinus :
    colorCoreToBdGLinear c (colorPolarizedGenerator c 3) = bdgSigmaMinus := by
  rw [colorCoreToBdGLinear, threeColorCausalMatrixEquiv_generator_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgSigmaMinus, Matrix.stdBasis, threeColorMatrixIndexEquiv]

@[simp] theorem colorCoreToBdGLinear_colorDirac
    (a b : ℚ) :
    colorCoreToBdGLinear c
        ⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩ =
      a • Matrix.stdBasis ℚ (Fin 2) (Fin 2) (0, 1) +
        b • Matrix.stdBasis ℚ (Fin 2) (Fin 2) (1, 0) := by
  simpa [colorCoreToBdGLinear] using
    (threeColorCausalMatrixEquiv_colorDirac c a b)

@[simp] theorem colorCoreToBdGLinear_balancedColorDirac
    (m : ℚ) :
    colorCoreToBdGLinear c
        ⟨colorDirac c m m, colorDirac_mem_colorCore c m m⟩ =
      diracOperator m := by
  rw [colorCoreToBdGLinear_colorDirac]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracOperator, Matrix.stdBasis, Matrix.add_apply]

@[simp] theorem bdgTau1_sq : bdgTau1 * bdgTau1 = (1 : BdGBlock ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTau3_sq : bdgTau3 * bdgTau3 = (1 : BdGBlock ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau3, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTau1_tau3_anticommute :
    bdgTau1 * bdgTau3 + bdgTau3 * bdgTau1 = (0 : BdGBlock ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau1, bdgTau3, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTauPlus_sq : bdgTauPlus * bdgTauPlus = (0 : BdGBlock ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTauPlus, bdgSigmaPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTauMinus_sq : bdgTauMinus * bdgTauMinus = (0 : BdGBlock ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTauMinus, bdgSigmaMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTauPlus_mul_tauMinus :
    bdgTauPlus * bdgTauMinus = bdgNPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTauPlus, bdgTauMinus, bdgSigmaPlus, bdgSigmaMinus,
      bdgNPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTauMinus_mul_tauPlus :
    bdgTauMinus * bdgTauPlus = bdgNMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTauPlus, bdgTauMinus, bdgSigmaPlus, bdgSigmaMinus,
      bdgNMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTau3_eq_nPlus_sub_nMinus :
    bdgTau3 = bdgNPlus - bdgNMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau3, bdgNPlus, bdgNMinus]

@[simp] theorem bdgTau1_flip_nPlus :
    bdgTau1 * bdgNPlus * bdgTau1 = bdgNMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau1, bdgNPlus, bdgNMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTau1_flip_tauPlus :
    bdgTau1 * bdgTauPlus * bdgTau1 = bdgTauMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau1, bdgTauPlus, bdgTauMinus, bdgSigmaPlus, bdgSigmaMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgTau1_flip_tau3 :
    bdgTau1 * bdgTau3 * bdgTau1 = -bdgTau3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgTau1, bdgTau3, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem bdgHadamard_sq :
    bdgHadamard * bdgHadamard = (2 : ℚ) • (1 : BdGBlock ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgHadamard, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem bdgHadamard_nullMetric_hadamard :
    bdgHadamard * bdgNullMetric * bdgHadamard =
      (2 : ℚ) • bdgDiagonalMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgHadamard, bdgNullMetric, bdgDiagonalMetric, bdgTau1,
      bdgTau3, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

end
end InfoGeometry.Physics.Bridge
