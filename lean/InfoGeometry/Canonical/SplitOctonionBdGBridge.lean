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

end
end InfoGeometry.Physics.Bridge
