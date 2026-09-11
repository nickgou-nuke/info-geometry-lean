import InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularWittForm

/-!
# Peirce/Witt sector identification

The left Peirce images of the native idempotents are identified with the two
coordinate-defined totally isotropic Witt sectors.  This is a linear
statement about images and quadratic support; no commutant assertion is made.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularPeirceWittIdentification

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionCircularWittForm

abbrev CZ := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

def leftPeircePlus : Submodule ℝ CZ :=
  LinearMap.range (leftMultiplication uPlus)

def leftPeirceMinus : Submodule ℝ CZ :=
  LinearMap.range (leftMultiplication uMinus)

def positivePeirceSector : Submodule ℝ CZ :=
  positiveCircularSubmodule.comap coordinateEquiv.toLinearMap

def negativePeirceSector : Submodule ℝ CZ :=
  negativeCircularSubmodule.comap coordinateEquiv.toLinearMap

private theorem leftCoordinate_uPlus_support (x : Coordinate) :
    leftCoordinateOperator uPlus x =
      fun i => if i.val < 4 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val < 4 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val < 4 <;> simp [hi]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val < 4 <;> simp [hi] }
  have hT : leftCoordinateOperator uPlus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (uPlus * frame i) =
          if i.val < 4 then Pi.single i 1 else 0 := by
      rw [uPlus_mul_frame]
      fin_cases i
      · simpa [frame] using coordinateEquiv_apply_frame 0
      · simpa [frame] using coordinateEquiv_apply_frame 1
      · simpa [frame] using coordinateEquiv_apply_frame 2
      · simpa [frame] using coordinateEquiv_apply_frame 3
      · simp
      · simp
      · simp
      · simp
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply, leftCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

private theorem leftCoordinate_uMinus_support (x : Coordinate) :
    leftCoordinateOperator uMinus x =
      fun i => if i.val ≥ 4 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val ≥ 4 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val ≥ 4 <;> simp [hi]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val ≥ 4 <;> simp [hi] }
  have hT : leftCoordinateOperator uMinus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (uMinus * frame i) =
          if i.val ≥ 4 then Pi.single i 1 else 0 := by
      rw [uMinus_mul_frame]
      fin_cases i
      · simp
      · simp
      · simp
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 4
      · simpa [frame] using coordinateEquiv_apply_frame 5
      · simpa [frame] using coordinateEquiv_apply_frame 6
      · simpa [frame] using coordinateEquiv_apply_frame 7
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply, leftCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

theorem leftPeircePlus_eq_positivePeirceSector :
    leftPeircePlus = positivePeirceSector := by
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    change coordinateEquiv (uPlus * Y) ∈ positiveCircularSubmodule
    rw [← coordinateEquiv.symm_apply_apply Y]
    rw [← leftCoordinateOperator_apply]
    rw [leftCoordinate_uPlus_support]
    intro i hi
    simp [hi]
  · intro X hX
    change coordinateEquiv X ∈ positiveCircularSubmodule at hX
    have hcoord :
        coordinateEquiv (uPlus * X) = coordinateEquiv X := by
      rw [← coordinateEquiv.symm_apply_apply X]
      rw [← leftCoordinateOperator_apply]
      rw [leftCoordinate_uPlus_support]
      funext i
      by_cases hi : i.val < 4
      · simp [hi]
      · have hz : coordinateEquiv X i = 0 := hX i (Nat.le_of_not_gt hi)
        simp [hi, hz]
    refine ⟨X, ?_⟩
    apply coordinateEquiv.injective
    simpa [leftCoordinateOperator_apply] using hcoord

theorem leftPeirceMinus_eq_negativePeirceSector :
    leftPeirceMinus = negativePeirceSector := by
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    change coordinateEquiv (uMinus * Y) ∈ negativeCircularSubmodule
    rw [← coordinateEquiv.symm_apply_apply Y]
    rw [← leftCoordinateOperator_apply]
    rw [leftCoordinate_uMinus_support]
    intro i hi
    simp [hi]
  · intro X hX
    change coordinateEquiv X ∈ negativeCircularSubmodule at hX
    have hcoord :
        coordinateEquiv (uMinus * X) = coordinateEquiv X := by
      rw [← coordinateEquiv.symm_apply_apply X]
      rw [← leftCoordinateOperator_apply]
      rw [leftCoordinate_uMinus_support]
      funext i
      by_cases hi : i.val ≥ 4
      · simp [hi]
      · have hz : coordinateEquiv X i = 0 := hX i (Nat.lt_of_not_ge hi)
        simp [hi, hz]
    refine ⟨X, ?_⟩
    apply coordinateEquiv.injective
    simpa [leftCoordinateOperator_apply] using hcoord

theorem leftPeircePlus_isTotallyIsotropic
    {X Y : CZ} (hX : X ∈ leftPeircePlus) (hY : Y ∈ leftPeircePlus) :
    circularPeircePolar (coordinateEquiv X) (coordinateEquiv Y) = 0 := by
  rw [leftPeircePlus_eq_positivePeirceSector] at hX hY
  exact positive_isTotallyIsotropic hX hY

theorem leftPeirceMinus_isTotallyIsotropic
    {X Y : CZ} (hX : X ∈ leftPeirceMinus) (hY : Y ∈ leftPeirceMinus) :
    circularPeircePolar (coordinateEquiv X) (coordinateEquiv Y) = 0 := by
  rw [leftPeirceMinus_eq_negativePeirceSector] at hX hY
  exact negative_isTotallyIsotropic hX hY

end InfoGeometry.Lie.SplitOctonionCircularPeirceWittIdentification
