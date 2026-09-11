import InfoGeometry.Lie.SplitOctonionImaginaryCircularForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exterior-power readout of the imaginary circular three-form

This owner connects the existing native exterior-power functional to the
already proved circular-basis coefficients.  It introduces no second
three-form and makes no stability or global `G₂` classification claim.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryCircularExterior

open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCrossTensor
open InfoGeometry.Lie.SplitOctonionImaginaryTensor
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryThreeForm
open InfoGeometry.Lie.SplitOctonionImaginaryCircularForm
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

def upperCombination (u : Fin 3 → ℝ) :
    SplitOctonionImaginaryCircularForm.Imaginary :=
  ∑ i : Fin 3, u i • upperAxis i

def lowerCombination (u : Fin 3 → ℝ) :
    SplitOctonionImaginaryCircularForm.Imaginary :=
  ∑ i : Fin 3, u i • lowerAxis i

/-! ## Intrinsic seven-dimensional circular decomposition -/

/- Every trace-zero Zorn element splits into its diagonal axis and the two
   circular root sectors.  The coefficients are the native Zorn coordinates;
   no additional coordinate carrier is introduced. -/
theorem imaginary_circular_decomposition
    (X : SplitOctonionImaginaryCircularForm.Imaginary) :
    X = X.1.a • diagonalAxis + upperCombination X.1.x + lowerCombination X.1.y := by
  apply imaginaryCoordLinearEquiv.injective
  apply Prod.ext
  · simp [imaginaryCoordLinearEquiv, diagonalAxis, upperCombination,
      lowerCombination, upperAxis, lowerAxis, rootPlus, rootMinus,
      quaternionAxis, ellAxis, axis, cartesianZornLinearEquiv,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def,
      InfoGeometry.Lie.SplitOctonionEllFlowOperator.diagEll,
      zornPlus, zornMinus]
  · apply Prod.ext
    · funext j
      fin_cases j <;>
        simp [imaginaryCoordLinearEquiv, diagonalAxis, upperCombination,
          lowerCombination, upperAxis, lowerAxis, rootPlus, rootMinus,
          quaternionAxis, ellAxis, axis, cartesianZornLinearEquiv,
          InfoGeometry.Canonical.ZornMatrix.coordEquiv,
          Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def,
          InfoGeometry.Lie.SplitOctonionEllFlowOperator.diagEll,
          zornPlus, zornMinus] <;> ring
    · funext j
      fin_cases j <;>
        simp [imaginaryCoordLinearEquiv, diagonalAxis, upperCombination,
          lowerCombination, upperAxis, lowerAxis, rootPlus, rootMinus,
          quaternionAxis, ellAxis, axis, cartesianZornLinearEquiv,
          InfoGeometry.Canonical.ZornMatrix.coordEquiv,
          Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def,
          InfoGeometry.Lie.SplitOctonionEllFlowOperator.diagEll,
          zornPlus, zornMinus] <;> ring

theorem exteriorMap_upper_upper_upper (i j k : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![upperAxis i, upperAxis j, upperAxis k]) =
      -(leviCivita3 k i j : ℝ) := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_upper_upper_upper i j k

theorem exteriorMap_lower_lower_lower (i j k : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![lowerAxis i, lowerAxis j, lowerAxis k]) =
      (leviCivita3 k i j : ℝ) := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_lower_lower_lower i j k

theorem exteriorMap_diagonal_upper_lower (i j : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![diagonalAxis, upperAxis i, lowerAxis j]) =
      -(if i = j then (1 : ℝ) else 0) := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_diagonal_upper_lower i j

theorem exteriorMap_diagonal_upper_upper (i j : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![diagonalAxis, upperAxis i, upperAxis j]) = 0 := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_diagonal_upper_upper i j

theorem exteriorMap_diagonal_lower_lower (i j : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![diagonalAxis, lowerAxis i, lowerAxis j]) = 0 := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_diagonal_lower_lower i j

theorem exteriorMap_upper_upper_lower (i j k : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![upperAxis i, upperAxis j, lowerAxis k]) = 0 := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_upper_upper_lower i j k

theorem exteriorMap_lower_lower_upper (i j k : Fin 3) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![lowerAxis i, lowerAxis j, upperAxis k]) = 0 := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    ← imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryThreeForm_lower_lower_upper i j k

/-! ## Global readout on the six-dimensional circular span -/

private theorem threeForm_add_left (X Y Z W :
    SplitOctonionImaginaryCircularForm.Imaginary) :
    imaginaryThreeForm (X + Y) Z W =
      imaginaryThreeForm X Z W + imaginaryThreeForm Y Z W := by
  simp only [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryCommutatorForm_add_left X Y Z W

private theorem threeForm_add_middle (X Y Z W :
    SplitOctonionImaginaryCircularForm.Imaginary) :
    imaginaryThreeForm X (Y + Z) W =
      imaginaryThreeForm X Y W + imaginaryThreeForm X Z W := by
  simp only [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryCommutatorForm_add_middle X Y Z W

private theorem threeForm_add_last (X Y Z W :
    SplitOctonionImaginaryCircularForm.Imaginary) :
    imaginaryThreeForm X Y (Z + W) =
      imaginaryThreeForm X Y Z + imaginaryThreeForm X Y W := by
  simp only [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact imaginaryCommutatorForm_add_last X Y Z W

private theorem threeForm_smul_left (r : ℝ) (X Y Z :
    SplitOctonionImaginaryCircularForm.Imaginary) :
    imaginaryThreeForm (r • X) Y Z = r * imaginaryThreeForm X Y Z := by
  simp only [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  simpa [smul_eq_mul] using imaginaryCommutatorForm_smul_left r X Y Z

private theorem threeForm_smul_middle (r : ℝ) (X Y Z :
    SplitOctonionImaginaryCircularForm.Imaginary) :
    imaginaryThreeForm X (r • Y) Z = r * imaginaryThreeForm X Y Z := by
  simp only [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  simpa [smul_eq_mul] using imaginaryCommutatorForm_smul_middle r X Y Z

private theorem threeForm_smul_last (r : ℝ) (X Y Z :
    SplitOctonionImaginaryCircularForm.Imaginary) :
    imaginaryThreeForm X Y (r • Z) = r * imaginaryThreeForm X Y Z := by
  simp only [imaginaryThreeForm_eq_imaginaryCommutatorForm]
  simpa [smul_eq_mul] using imaginaryCommutatorForm_smul_last r X Y Z

theorem threeForm_upperCombination (u v w : Fin 3 → ℝ) :
    imaginaryThreeForm (upperCombination u) (upperCombination v)
        (upperCombination w) =
      -∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        u i * v j * w k * (leviCivita3 k i j : ℝ) := by
  simp [upperCombination, threeForm_add_left, threeForm_add_middle,
    threeForm_add_last, threeForm_smul_left, threeForm_smul_middle,
    threeForm_smul_last, imaginaryThreeForm_upper_upper_upper,
    Fin.sum_univ_three]
  ring

theorem threeForm_lowerCombination (u v w : Fin 3 → ℝ) :
    imaginaryThreeForm (lowerCombination u) (lowerCombination v)
        (lowerCombination w) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        u i * v j * w k * (leviCivita3 k i j : ℝ) := by
  simp [lowerCombination, threeForm_add_left, threeForm_add_middle,
    threeForm_add_last, threeForm_smul_left, threeForm_smul_middle,
    threeForm_smul_last, imaginaryThreeForm_lower_lower_lower,
    Fin.sum_univ_three]
  ring

private theorem threeForm_upper_lower_upper_zero (i j k : Fin 3) :
    imaginaryThreeForm (upperAxis i) (lowerAxis j) (upperAxis k) = 0 := by
  calc
    imaginaryThreeForm (upperAxis i) (lowerAxis j) (upperAxis k) =
        imaginaryThreeForm (lowerAxis j) (upperAxis k) (upperAxis i) :=
      imaginaryThreeForm_cyclic _ _ _
    _ = imaginaryThreeForm (upperAxis k) (upperAxis i) (lowerAxis j) :=
      imaginaryThreeForm_cyclic _ _ _
    _ = 0 := imaginaryThreeForm_upper_upper_lower k i j

private theorem threeForm_lower_upper_upper_zero (i j k : Fin 3) :
    imaginaryThreeForm (lowerAxis i) (upperAxis j) (upperAxis k) = 0 := by
  calc
    imaginaryThreeForm (lowerAxis i) (upperAxis j) (upperAxis k) =
        imaginaryThreeForm (upperAxis j) (upperAxis k) (lowerAxis i) :=
      imaginaryThreeForm_cyclic _ _ _
    _ = 0 := imaginaryThreeForm_upper_upper_lower j k i

private theorem threeForm_upper_lower_lower_zero (i j k : Fin 3) :
    imaginaryThreeForm (upperAxis i) (lowerAxis j) (lowerAxis k) = 0 := by
  calc
    imaginaryThreeForm (upperAxis i) (lowerAxis j) (lowerAxis k) =
        imaginaryThreeForm (lowerAxis j) (lowerAxis k) (upperAxis i) :=
      imaginaryThreeForm_cyclic _ _ _
    _ = 0 := imaginaryThreeForm_lower_lower_upper j k i

private theorem threeForm_lower_upper_lower_zero (i j k : Fin 3) :
    imaginaryThreeForm (lowerAxis i) (upperAxis j) (lowerAxis k) = 0 := by
  calc
    imaginaryThreeForm (lowerAxis i) (upperAxis j) (lowerAxis k) =
        imaginaryThreeForm (upperAxis j) (lowerAxis k) (lowerAxis i) :=
      imaginaryThreeForm_cyclic _ _ _
    _ = 0 := threeForm_upper_lower_lower_zero j k i

/-- On the full six-dimensional circular span, the native imaginary
three-form is exactly the sum of its two pure cubic channels.  The upper
volume carries the native minus sign and every mixed channel vanishes. -/
theorem threeForm_circular_decomposition
    (u₁ u₂ u₃ l₁ l₂ l₃ : Fin 3 → ℝ) :
    imaginaryThreeForm
        (upperCombination u₁ + lowerCombination l₁)
        (upperCombination u₂ + lowerCombination l₂)
        (upperCombination u₃ + lowerCombination l₃) =
      -(∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          u₁ i * u₂ j * u₃ k * (leviCivita3 k i j : ℝ)) +
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          l₁ i * l₂ j * l₃ k * (leviCivita3 k i j : ℝ) := by
  simp [upperCombination, lowerCombination, threeForm_add_left,
    threeForm_add_middle, threeForm_add_last, threeForm_smul_left,
    threeForm_smul_middle, threeForm_smul_last,
    imaginaryThreeForm_upper_upper_upper,
    imaginaryThreeForm_lower_lower_lower,
    imaginaryThreeForm_upper_upper_lower,
    imaginaryThreeForm_lower_lower_upper,
    threeForm_upper_lower_upper_zero, threeForm_lower_upper_upper_zero,
    threeForm_upper_lower_lower_zero, threeForm_lower_upper_lower_zero,
    Fin.sum_univ_three]
  ring

/-! ## Native volume-form readout -/

theorem leviCivita_sum_eq_nativeVolumeForm (u v w : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      u i * v j * w k * (leviCivita3 k i j : ℝ)) =
      nativeVolumeForm ![u, v, w] := by
  rw [nativeVolumeForm_apply_eq_scalarTriple]
  rw [← nativeScalarTriple_cyclic]
  rw [nativeScalarTriple_eq_leviCivita3]
  simp [Fin.sum_univ_three]
  ring

/-- The restriction of the native imaginary three-form to the circular
root span is the difference of the native upper and lower volume forms. -/
theorem threeForm_circular_decomposition_volume
    (u₁ u₂ u₃ l₁ l₂ l₃ : Fin 3 → ℝ) :
    imaginaryThreeForm
        (upperCombination u₁ + lowerCombination l₁)
        (upperCombination u₂ + lowerCombination l₂)
        (upperCombination u₃ + lowerCombination l₃) =
      -nativeVolumeForm ![u₁, u₂, u₃] +
        nativeVolumeForm ![l₁, l₂, l₃] := by
  rw [threeForm_circular_decomposition,
    leviCivita_sum_eq_nativeVolumeForm,
    leviCivita_sum_eq_nativeVolumeForm]

end InfoGeometry.Lie.SplitOctonionImaginaryCircularExterior
