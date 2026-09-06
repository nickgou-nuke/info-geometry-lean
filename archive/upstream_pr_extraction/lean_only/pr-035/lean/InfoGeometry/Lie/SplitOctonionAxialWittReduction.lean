import InfoGeometry.Lie.SplitOctonionAxialSupportGrading
import InfoGeometry.Algebra.Zorn.Basic

/-!
# Native `(1,1) + (3,3)` reduction of the diagonal Zorn norm

The tripotent zero projector extracts the two diagonal coordinates, while its
Drazin support `Q = T²` extracts the six upper/lower vector coordinates.  This
file proves the resulting coordinate and quadratic splitting on the actual
canonical Zorn carrier.

The six-dimensional active sector is identified with three real Witt pairs
`(x,y)`.  No orthogonal-group, spin-group, or twistor-group equivalence is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialWittReduction

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Lie.SplitOctonionAxialSupportGrading

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev ActiveSector := LinearMap.range axialActiveSupport
abbrev WittCoordinates := (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- The Drazin active support is exactly the pair of upper and lower
three-vector coordinates. -/
def activeSectorEquiv : ActiveSector ≃ₗ[ℝ] WittCoordinates where
  toFun X := (X.1.x, X.1.y)
  invFun xy :=
    ⟨{ a := 0, b := 0, x := xy.1, y := xy.2 }, by
      rw [LinearMap.mem_range]
      refine ⟨{ a := 0, b := 0, x := xy.1, y := xy.2 }, ?_⟩
      rw [axialActiveSupport_apply]⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨X, Y, hY⟩
    dsimp
    rw [axialActiveSupport_apply] at hY
    rw [← hY]
  right_inv xy := rfl

@[simp] theorem activeSector_finrank :
    Module.finrank ℝ ActiveSector = 6 := by
  rw [activeSectorEquiv.finrank_eq]
  simp

/-- The signed Witt grading on the six active coordinates. -/
def signedWittGrading : WittCoordinates →ₗ[ℝ] WittCoordinates where
  toFun xy := (xy.1, -xy.2)
  map_add' X Y := by ext i <;> simp [add_comm]
  map_smul' r X := by ext i <;> simp

/-- Restriction of the axial tripotent to its active support. -/
def axialGradingOnActive : ActiveSector →ₗ[ℝ] ActiveSector where
  toFun X :=
    ⟨axialGrading X.1, by
      rw [LinearMap.mem_range]
      refine ⟨axialGrading X.1, ?_⟩
      ext i <;>
        simp [axialActiveSupport_apply, axialGrading]⟩
  map_add' X Y := by
    apply Subtype.ext
    exact map_add axialGrading X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact map_smul axialGrading r X.1

/-- On Drazin support, the tripotent is exactly the `(+1,-1)` Witt
involution. -/
theorem activeSectorEquiv_intertwines_grading (X : ActiveSector) :
    activeSectorEquiv (axialGradingOnActive X) =
      signedWittGrading (activeSectorEquiv X) := by
  rfl

/-- Every Zorn vector is the sum of its stationary diagonal component and its
active Drazin-support component. -/
theorem axial_PZero_add_activeSupport (X : CZ) :
    axialPZero X + axialActiveSupport X = X := by
  rw [axialPZero_apply, axialActiveSupport_apply]
  ext i <;> simp [ZornMatrix.add_def]

/-- The stationary and active coordinate projections annihilate each other. -/
@[simp] theorem axialPZero_activeSupport (X : CZ) :
    axialPZero (axialActiveSupport X) = 0 := by
  rw [axialActiveSupport_apply, axialPZero_apply]
  rfl

@[simp] theorem axialActiveSupport_PZero (X : CZ) :
    axialActiveSupport (axialPZero X) = 0 := by
  rw [axialPZero_apply, axialActiveSupport_apply]
  rfl

/-- The determinant on the stationary sector is the hyperbolic-plane form
`a*b`. -/
theorem detZ_axialPZero (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (axialPZero X) = X.a * X.b := by
  rw [axialPZero_apply]
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, ZornMatrix.dot]

/-- The determinant on Drazin support is the three-Witt-pair form
`-x dot y`. -/
theorem detZ_axialActiveSupport (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (axialActiveSupport X) =
      -ZornMatrix.dot X.x X.y := by
  rw [axialActiveSupport_apply]
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ]

/-- Exact quadratic splitting of the full `(4,4)` Zorn norm into its
stationary `(1,1)` and active three-Witt-pair contributions. -/
theorem detZ_eq_PZero_add_active (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (axialPZero X) +
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (axialActiveSupport X) := by
  rw [detZ_axialPZero, detZ_axialActiveSupport]
  unfold InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
  ring

end InfoGeometry.Lie.SplitOctonionAxialWittReduction
