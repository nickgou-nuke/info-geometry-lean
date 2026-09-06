import proofs.ChiralStokesCoordinates

/-!
# Pauli/Stokes basis for two-sheet operators

This owner identifies the four matrix-valued Stokes coordinates with the
operator basis `I, Γ, J, -i Γ J`.  Krein, Nambu, and Tomita structures are
intentionally not imported here.
-/

noncomputable section
namespace ChiralStokesPauliBasis

open TwoSheetThreeColorWeyl
open TwoSheetOperatorCoordinates
open ChiralStokesCoordinates

/-- The composite linear coordinate equivalence from six-state operators to
matrix-valued Stokes coordinates. -/
def operatorStokesLinearEquiv :
    M6C ≃ₗ[ℂ] StokesQuad :=
  blockLinearEquiv.trans stokesLinearEquiv

/-- The Pauli/Stokes reconstruction in the original two-sheet matrix carrier. -/
def assembleStokes (S : StokesQuad) : M6C :=
  tensor (1 : M2C) S.1 +
    tensor sheetGamma S.2.1 +
    tensor sheetFlip S.2.2.1 +
    (-Complex.I) • tensor (sheetGamma * sheetFlip) S.2.2.2

/-- The complex phase Pauli matrix is `-i Γ J`. -/
def sheetPauli2 : M2C := (-Complex.I) • (sheetGamma * sheetFlip)

theorem sheetPauli2_eq_neg_i_parity_flip :
    sheetPauli2 = (-Complex.I) • (sheetGamma * sheetFlip) := rfl

theorem assembleStokes_eq_pauli_expansion (S : StokesQuad) :
    assembleStokes S =
      tensor (1 : M2C) S.1 +
        tensor sheetGamma S.2.1 +
        tensor sheetFlip S.2.2.1 +
        tensor sheetPauli2 S.2.2.2 := by
  ext ⟨s, i⟩ ⟨t, j⟩
  simp [assembleStokes, sheetPauli2, tensor, Matrix.smul_apply]
  ring

theorem assembleStokes_eq_block_reconstruction (S : StokesQuad) :
    assembleStokes S =
      assembleBlocks (stokesReconstruct S) := by
  ext ⟨s, i⟩ ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [assembleStokes, assembleBlocks, stokesReconstruct, tensor,
      sheetGamma, sheetFlip, sheetPlus, sheetMinus, Matrix.smul_apply]
  <;> ring

theorem stokes_even_odd_decomposition (S : StokesQuad) :
    assembleStokes S =
      (tensor (1 : M2C) S.1 + tensor sheetGamma S.2.1) +
      (tensor sheetFlip S.2.2.1 + tensor sheetPauli2 S.2.2.2) := by
  rw [assembleStokes_eq_pauli_expansion]
  simp [add_assoc]

end ChiralStokesPauliBasis
end noncomputable section
