import InfoGeometry.Lie.SplitOctonionAxialCartanFlow

/-!
# Exact dimensions of the diagonal axial trifactor sectors

The three sectors are the actual ranges of the native polynomial projectors.
Coordinate linear equivalences prove their dimensions without an assumed basis
packet: upper and lower sectors are `Fin 3 → ℝ`, while the stationary sector
is the pair of diagonal coordinates.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialFlowDecomposition

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor

abbrev CZ := ZornMatrix ℝ

abbrev positiveSector := LinearMap.range axialPPlus
abbrev zeroSector := LinearMap.range axialPZero
abbrev negativeSector := LinearMap.range axialPMinus

/-- Upper/color coordinates identify the positive axial sector with three real
coordinates. -/
def positiveSectorEquiv : positiveSector ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X := X.1.x
  invFun x :=
    ⟨{ a := 0, b := 0, x := x, y := 0 }, by
      rw [LinearMap.mem_range]
      refine ⟨{ a := 0, b := 0, x := x, y := 0 }, ?_⟩
      rw [axialPPlus_apply, colorProject_apply]⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [axialPPlus_apply, colorProject_apply] at hY
    rw [← hY]
  right_inv x := rfl

/-- Lower/anticolor coordinates identify the negative axial sector with three
real coordinates. -/
def negativeSectorEquiv : negativeSector ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X := X.1.y
  invFun y :=
    ⟨{ a := 0, b := 0, x := 0, y := y }, by
      rw [LinearMap.mem_range]
      refine ⟨{ a := 0, b := 0, x := 0, y := y }, ?_⟩
      rw [axialPMinus_apply, anticolorProject_apply]⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [axialPMinus_apply, anticolorProject_apply] at hY
    rw [← hY]
  right_inv y := rfl

/-- The stationary/Drazin-defect coordinates are exactly the two diagonal real
coordinates. -/
def zeroSectorEquiv : zeroSector ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun X := (X.1.a, X.1.b)
  invFun ab :=
    ⟨{ a := ab.1, b := ab.2, x := 0, y := 0 }, by
      rw [LinearMap.mem_range]
      refine ⟨{ a := ab.1, b := ab.2, x := 0, y := 0 }, ?_⟩
      rw [axialPZero_apply]⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [axialPZero_apply] at hY
    rw [← hY]
  right_inv ab := rfl

@[simp] theorem positiveSector_finrank :
    Module.finrank ℝ positiveSector = 3 := by
  rw [positiveSectorEquiv.finrank_eq]
  simp

@[simp] theorem zeroSector_finrank :
    Module.finrank ℝ zeroSector = 2 := by
  rw [zeroSectorEquiv.finrank_eq]
  simp

@[simp] theorem negativeSector_finrank :
    Module.finrank ℝ negativeSector = 3 := by
  rw [negativeSectorEquiv.finrank_eq]
  simp

end InfoGeometry.Lie.SplitOctonionAxialFlowDecomposition
