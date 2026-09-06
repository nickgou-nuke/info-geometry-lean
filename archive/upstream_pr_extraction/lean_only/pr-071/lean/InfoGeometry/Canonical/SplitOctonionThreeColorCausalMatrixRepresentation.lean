import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis

namespace InfoGeometry.Canonical

open scoped Matrix

noncomputable section

/-- The four generator indices of the coloured core, ordered as
`n₊, n₋, σ₊, σ₋`. -/
def threeColorMatrixIndexEquiv : Fin 4 ≃ (Fin 2 × Fin 2) where
  toFun
    | ⟨0, _⟩ => (0, 0)
    | ⟨1, _⟩ => (1, 1)
    | ⟨2, _⟩ => (0, 1)
    | ⟨3, _⟩ => (1, 0)
    | _ => (0, 0)
  invFun
    | (0, 0) => 0
    | (1, 1) => 1
    | (0, 1) => 2
    | (1, 0) => 3
    | _ => 0
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro ij
    cases ij with
    | mk i j =>
        fin_cases i <;> fin_cases j <;> rfl

/-- A native basis of the coloured core, obtained from the finite-dimensional
vector-space structure already proved in the split-octonion core owner. -/
noncomputable def threeColorCoreMatrixBasis
    (c : SplitOctonionColour) :
    Module.Basis (Fin 4) ℚ (colorCore c) :=
  colorPolarizedBasis c

/-- The canonical linear matrix representation of a coloured core. -/
noncomputable def threeColorCausalMatrixEquiv
    (c : SplitOctonionColour) :
    colorCore c ≃ₗ[ℚ] Matrix (Fin 2) (Fin 2) ℚ :=
  (threeColorCoreMatrixBasis c).equiv
    (Matrix.stdBasis ℚ (Fin 2) (Fin 2))
    threeColorMatrixIndexEquiv

@[simp] theorem threeColorCausalMatrixEquiv_basis_apply
    (c : SplitOctonionColour) (i : Fin 4) :
    threeColorCausalMatrixEquiv c ((threeColorCoreMatrixBasis c) i) =
      Matrix.stdBasis ℚ (Fin 2) (Fin 2) (threeColorMatrixIndexEquiv i) := by
  simpa [threeColorCausalMatrixEquiv, threeColorCoreMatrixBasis] using
    (Module.Basis.equiv_apply (colorPolarizedBasis c) i
      (Matrix.stdBasis ℚ (Fin 2) (Fin 2)) threeColorMatrixIndexEquiv)

@[simp] theorem threeColorCausalMatrixEquiv_generator_apply
    (c : SplitOctonionColour) (i : Fin 4) :
    threeColorCausalMatrixEquiv c (colorPolarizedGenerator c i) =
      Matrix.stdBasis ℚ (Fin 2) (Fin 2) (threeColorMatrixIndexEquiv i) := by
  simpa [threeColorCoreMatrixBasis] using
    threeColorCausalMatrixEquiv_basis_apply c i

@[simp] theorem threeColorCausalMatrixEquiv_injective
    (c : SplitOctonionColour) :
    Function.Injective (threeColorCausalMatrixEquiv c) :=
  (threeColorCausalMatrixEquiv c).injective

@[simp] theorem threeColorCausalMatrixEquiv_surjective
    (c : SplitOctonionColour) :
    Function.Surjective (threeColorCausalMatrixEquiv c) :=
  (threeColorCausalMatrixEquiv c).surjective

end

end InfoGeometry.Canonical
