import proofs.TwoSheetOperatorCoordinates

/-!
# Matrix-valued Stokes coordinates for two sheets

The four colour-valued coordinates are the sheet-blind, sheet-imbalance,
real sheet-changing, and phase sheet-changing components.
-/

noncomputable section
namespace ChiralStokesCoordinates

open TwoSheetThreeColorWeyl
open TwoSheetOperatorCoordinates

abbrev StokesQuad := M3C × M3C × M3C × M3C

/-- Stokes coordinates `(A₀,A₃,A₁,A₂)` extracted from the four sheet blocks. -/
def stokesCoordinates (B : BlockQuad) : StokesQuad :=
  ((2 : ℂ)⁻¹ • (B.1 + B.2.2.2),
    (2 : ℂ)⁻¹ • (B.1 - B.2.2.2),
    (2 : ℂ)⁻¹ • (B.2.1 + B.2.2.1),
    (2 * Complex.I)⁻¹ • (B.2.2.1 - B.2.1))

/-- Reconstruct sheet blocks from Stokes coordinates. -/
def stokesReconstruct (S : StokesQuad) : BlockQuad :=
  (S.1 + S.2.1,
    S.2.2.1 - Complex.I • S.2.2.2,
    S.2.2.1 + Complex.I • S.2.2.2,
    S.1 - S.2.1)

theorem stokesReconstruct_coordinates (B : BlockQuad) :
    stokesReconstruct (stokesCoordinates B) = B := by
  rcases B with ⟨B00, B01, B10, B11⟩
  apply Prod.ext
  · ext i j
    dsimp [stokesReconstruct, stokesCoordinates]
    ring
  · apply Prod.ext
    · ext i j
      dsimp [stokesReconstruct, stokesCoordinates]
      field_simp
      ring
    · apply Prod.ext
      · ext i j
        dsimp [stokesReconstruct, stokesCoordinates]
        field_simp
        ring
      · ext i j
        dsimp [stokesReconstruct, stokesCoordinates]
        ring

theorem stokesCoordinates_reconstruct (S : StokesQuad) :
    stokesCoordinates (stokesReconstruct S) = S := by
  rcases S with ⟨A0, A3, A1, A2⟩
  apply Prod.ext
  · ext i j
    dsimp [stokesCoordinates, stokesReconstruct]
    ring
  · apply Prod.ext
    · ext i j
      dsimp [stokesCoordinates, stokesReconstruct]
      ring
    · apply Prod.ext
      · ext i j
        dsimp [stokesCoordinates, stokesReconstruct]
        ring
      · ext i j
        dsimp [stokesCoordinates, stokesReconstruct]
        field_simp
        ring

def stokesLinearEquiv : BlockQuad ≃ₗ[ℂ] StokesQuad where
  toFun := stokesCoordinates
  invFun := stokesReconstruct
  map_add' B C := by
    apply Prod.ext
    · ext i j
      dsimp [stokesCoordinates]
      ring
    · apply Prod.ext
      · ext i j
        dsimp [stokesCoordinates]
        ring
      · apply Prod.ext
        · ext i j
          dsimp [stokesCoordinates]
          ring
        · ext i j
          dsimp [stokesCoordinates]
          ring
  map_smul' c B := by
    apply Prod.ext
    · ext i j
      dsimp [stokesCoordinates]
      ring
    · apply Prod.ext
      · ext i j
        dsimp [stokesCoordinates]
        ring
      · apply Prod.ext
        · ext i j
          dsimp [stokesCoordinates]
          ring
        · ext i j
          dsimp [stokesCoordinates]
          ring
  left_inv := stokesReconstruct_coordinates
  right_inv := stokesCoordinates_reconstruct

end ChiralStokesCoordinates
end noncomputable section
