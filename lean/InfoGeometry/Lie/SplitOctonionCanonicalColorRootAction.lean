import InfoGeometry.Canonical.CanonicalChiralZornEquivariance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-!
# Canonical colour automorphisms on circular root generators

These readouts are the concrete generator-level bridge used to connect the
order-six canonical automorphism action with the already-owned circular root
coordinates.  They avoid unfolding the hexagon carrier itself.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Physics.Octonion
open InfoGeometry.Physics.Octonion.ChiralZornMatrix
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-- Permutation of the ordered circular frame induced by the native colour
cycle.  The two diagonal Peirce positions are fixed. -/
def cycleFrameIndex : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 4
  | 5 => 6
  | 6 => 7
  | 7 => 5
  | _ => 0

/-- Permutation of the ordered circular frame induced by the native sheet
reflection. -/
def reflectionFrameIndex : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 5
  | 2 => 7
  | 3 => 6
  | 4 => 0
  | 5 => 1
  | 6 => 3
  | 7 => 2
  | _ => 0
open InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon

theorem canonicalColorCycle_rootPlus (i : Fin 3) :
    canonicalColorCycle (cartesianZornLinearEquiv (rootPlus i)) =
      cartesianZornLinearEquiv (rootPlus (nextColor i)) := by
  fin_cases i <;>
    ext j <;>
    simp [canonicalColorCycle, canonicalChiralMulEquiv,
      ChiralZornMatrix.rotateMulEquiv_apply, ChiralZornMatrix.rotateColor,
      InfoGeometry.Physics.Octonion.prevColor, cartesianZornLinearEquiv,
      rootPlus, quaternionAxis, ellAxis, axis, Equiv.smul_def,
      ZornMatrix.coordEquiv] <;>
    try { fin_cases j <;> simp [nextColor, reflectColor, Pi.single_apply] <;> norm_num }

theorem canonicalColorCycle_rootMinus (i : Fin 3) :
    canonicalColorCycle (cartesianZornLinearEquiv (rootMinus i)) =
      cartesianZornLinearEquiv (rootMinus (nextColor i)) := by
  fin_cases i <;>
    ext j <;>
    simp [canonicalColorCycle, canonicalChiralMulEquiv,
      ChiralZornMatrix.rotateMulEquiv_apply, ChiralZornMatrix.rotateColor,
      InfoGeometry.Physics.Octonion.prevColor, cartesianZornLinearEquiv,
      rootMinus, quaternionAxis, ellAxis, axis, Equiv.smul_def,
      ZornMatrix.coordEquiv] <;>
    try { fin_cases j <;> simp [nextColor, reflectColor, Pi.single_apply] <;> norm_num }

theorem canonicalColorReflection_rootPlus (i : Fin 3) :
    canonicalColorReflection (cartesianZornLinearEquiv (rootPlus i)) =
      cartesianZornLinearEquiv (rootMinus (reflectColor i)) := by
  fin_cases i <;>
    ext j <;>
    simp [canonicalColorReflection, canonicalChiralMulEquiv,
      ChiralZornMatrix.reflectMulEquiv_apply, ChiralZornMatrix.reflect,
      ChiralZornMatrix.reflectColor, cartesianZornLinearEquiv, rootPlus,
      rootMinus, quaternionAxis, ellAxis, axis, Equiv.smul_def,
      ZornMatrix.coordEquiv] <;>
    try { fin_cases j <;> simp [nextColor, reflectColor, Pi.single_apply] <;> norm_num }

theorem canonicalColorReflection_rootMinus (i : Fin 3) :
    canonicalColorReflection (cartesianZornLinearEquiv (rootMinus i)) =
      cartesianZornLinearEquiv (rootPlus (reflectColor i)) := by
  fin_cases i <;>
    ext j <;>
    simp [canonicalColorReflection, canonicalChiralMulEquiv,
      ChiralZornMatrix.reflectMulEquiv_apply, ChiralZornMatrix.reflect,
      ChiralZornMatrix.reflectColor, cartesianZornLinearEquiv, rootPlus,
      rootMinus, quaternionAxis, ellAxis, axis, Equiv.smul_def,
      ZornMatrix.coordEquiv] <;>
    try { fin_cases j <;> simp [nextColor, reflectColor, Pi.single_apply] <;> norm_num }

theorem canonicalColorCycle_circularChannel_positive (i : HexColor) :
    canonicalColorCycle (circularChannel (positiveVertex i)) =
      circularChannel (colorRotation (positiveVertex i)) := by
  calc
    canonicalColorCycle (circularChannel (positiveVertex i)) =
        canonicalColorCycle (cartesianZornLinearEquiv (rootPlus i)) := by
      rw [circularChannel_positive]
    _ = cartesianZornLinearEquiv (rootPlus (nextColor i)) :=
      canonicalColorCycle_rootPlus i
    _ = circularChannel (positiveVertex (nextColor i)) := by
      rw [circularChannel_positive]
    _ = circularChannel (colorRotation (positiveVertex i)) := by
      rw [colorRotation_positive]
      fin_cases i <;> rfl

theorem canonicalColorCycle_circularChannel_negative (i : HexColor) :
    canonicalColorCycle (circularChannel (negativeVertex i)) =
      circularChannel (colorRotation (negativeVertex i)) := by
  calc
    canonicalColorCycle (circularChannel (negativeVertex i)) =
        canonicalColorCycle (cartesianZornLinearEquiv (rootMinus i)) := by
      rw [circularChannel_negative]
    _ = cartesianZornLinearEquiv (rootMinus (nextColor i)) :=
      canonicalColorCycle_rootMinus i
    _ = circularChannel (negativeVertex (nextColor i)) := by
      rw [circularChannel_negative]
    _ = circularChannel (colorRotation (negativeVertex i)) := by
      rw [colorRotation_negative]
      fin_cases i <;> rfl

theorem canonicalColorCycle_circularChannel (n : HexIndex) :
    canonicalColorCycle (circularChannel n) =
      circularChannel (colorRotation n) := by
  fin_cases n
  · change canonicalColorCycle (circularChannel (positiveVertex 0)) =
      circularChannel (colorRotation (positiveVertex 0))
    exact canonicalColorCycle_circularChannel_positive 0
  · change canonicalColorCycle (circularChannel (negativeVertex 2)) =
      circularChannel (colorRotation (negativeVertex 2))
    exact canonicalColorCycle_circularChannel_negative 2
  · change canonicalColorCycle (circularChannel (positiveVertex 1)) =
      circularChannel (colorRotation (positiveVertex 1))
    exact canonicalColorCycle_circularChannel_positive 1
  · change canonicalColorCycle (circularChannel (negativeVertex 0)) =
      circularChannel (colorRotation (negativeVertex 0))
    exact canonicalColorCycle_circularChannel_negative 0
  · change canonicalColorCycle (circularChannel (positiveVertex 2)) =
      circularChannel (colorRotation (positiveVertex 2))
    exact canonicalColorCycle_circularChannel_positive 2
  · change canonicalColorCycle (circularChannel (negativeVertex 1)) =
      circularChannel (colorRotation (negativeVertex 1))
    exact canonicalColorCycle_circularChannel_negative 1

/-! Multiplication equivariance on the four circular root sectors. -/

theorem canonicalColorCycle_rootPlus_mul (i j : Fin 3) :
    canonicalColorCycle
        (cartesianZornLinearEquiv (rootPlus i) *
          cartesianZornLinearEquiv (rootPlus j)) =
      cartesianZornLinearEquiv (rootPlus (nextColor i)) *
        cartesianZornLinearEquiv (rootPlus (nextColor j)) := by
  rw [canonicalColorCycle_map_mul, canonicalColorCycle_rootPlus,
    canonicalColorCycle_rootPlus]

theorem canonicalColorCycle_rootMinus_mul (i j : Fin 3) :
    canonicalColorCycle
        (cartesianZornLinearEquiv (rootMinus i) *
          cartesianZornLinearEquiv (rootMinus j)) =
      cartesianZornLinearEquiv (rootMinus (nextColor i)) *
        cartesianZornLinearEquiv (rootMinus (nextColor j)) := by
  rw [canonicalColorCycle_map_mul, canonicalColorCycle_rootMinus,
    canonicalColorCycle_rootMinus]

theorem canonicalColorCycle_rootPlus_rootMinus_mul (i j : Fin 3) :
    canonicalColorCycle
        (cartesianZornLinearEquiv (rootPlus i) *
          cartesianZornLinearEquiv (rootMinus j)) =
      cartesianZornLinearEquiv (rootPlus (nextColor i)) *
        cartesianZornLinearEquiv (rootMinus (nextColor j)) := by
  rw [canonicalColorCycle_map_mul, canonicalColorCycle_rootPlus,
    canonicalColorCycle_rootMinus]

theorem canonicalColorCycle_rootMinus_rootPlus_mul (i j : Fin 3) :
    canonicalColorCycle
        (cartesianZornLinearEquiv (rootMinus i) *
          cartesianZornLinearEquiv (rootPlus j)) =
      cartesianZornLinearEquiv (rootMinus (nextColor i)) *
        cartesianZornLinearEquiv (rootPlus (nextColor j)) := by
  rw [canonicalColorCycle_map_mul, canonicalColorCycle_rootMinus,
    canonicalColorCycle_rootPlus]

theorem canonicalColorReflection_rootPlus_mul (i j : Fin 3) :
    canonicalColorReflection
        (cartesianZornLinearEquiv (rootPlus i) *
          cartesianZornLinearEquiv (rootPlus j)) =
      cartesianZornLinearEquiv (rootMinus (reflectColor i)) *
        cartesianZornLinearEquiv (rootMinus (reflectColor j)) := by
  rw [canonicalColorReflection_map_mul, canonicalColorReflection_rootPlus,
    canonicalColorReflection_rootPlus]

theorem canonicalColorReflection_rootMinus_mul (i j : Fin 3) :
    canonicalColorReflection
        (cartesianZornLinearEquiv (rootMinus i) *
          cartesianZornLinearEquiv (rootMinus j)) =
      cartesianZornLinearEquiv (rootPlus (reflectColor i)) *
        cartesianZornLinearEquiv (rootPlus (reflectColor j)) := by
  rw [canonicalColorReflection_map_mul, canonicalColorReflection_rootMinus,
    canonicalColorReflection_rootMinus]

theorem canonicalColorReflection_rootPlus_rootMinus_mul (i j : Fin 3) :
    canonicalColorReflection
        (cartesianZornLinearEquiv (rootPlus i) *
          cartesianZornLinearEquiv (rootMinus j)) =
      cartesianZornLinearEquiv (rootMinus (reflectColor i)) *
        cartesianZornLinearEquiv (rootPlus (reflectColor j)) := by
  rw [canonicalColorReflection_map_mul, canonicalColorReflection_rootPlus,
    canonicalColorReflection_rootMinus]

theorem canonicalColorReflection_rootMinus_rootPlus_mul (i j : Fin 3) :
    canonicalColorReflection
        (cartesianZornLinearEquiv (rootMinus i) *
          cartesianZornLinearEquiv (rootPlus j)) =
      cartesianZornLinearEquiv (rootPlus (reflectColor i)) *
        cartesianZornLinearEquiv (rootMinus (reflectColor j)) := by
  rw [canonicalColorReflection_map_mul, canonicalColorReflection_rootMinus,
    canonicalColorReflection_rootPlus]

theorem canonicalColorReflection_circularChannel (n : HexIndex) :
    canonicalColorReflection (circularChannel n) =
      circularChannel (sheetReflection n) := by
  fin_cases n
  · change canonicalColorReflection (circularChannel (positiveVertex 0)) =
      circularChannel (sheetReflection (positiveVertex 0))
    rw [circularChannel_positive, canonicalColorReflection_rootPlus]
    rw [← circularChannel_negative, sheetReflection_positive]
    rfl
  · change canonicalColorReflection (circularChannel (negativeVertex 2)) =
      circularChannel (sheetReflection (negativeVertex 2))
    rw [circularChannel_negative, canonicalColorReflection_rootMinus]
    rw [← circularChannel_positive, sheetReflection_negative]
    rfl

  · change canonicalColorReflection (circularChannel (positiveVertex 1)) =
      circularChannel (sheetReflection (positiveVertex 1))
    rw [circularChannel_positive, canonicalColorReflection_rootPlus]
    rw [← circularChannel_negative, sheetReflection_positive]
    rfl
  · change canonicalColorReflection (circularChannel (negativeVertex 0)) =
      circularChannel (sheetReflection (negativeVertex 0))
    rw [circularChannel_negative, canonicalColorReflection_rootMinus]
    rw [← circularChannel_positive, sheetReflection_negative]
    rfl
  · change canonicalColorReflection (circularChannel (positiveVertex 2)) =
      circularChannel (sheetReflection (positiveVertex 2))
    rw [circularChannel_positive, canonicalColorReflection_rootPlus]
    rw [← circularChannel_negative, sheetReflection_positive]
    rfl
  · change canonicalColorReflection (circularChannel (negativeVertex 1)) =
      circularChannel (sheetReflection (negativeVertex 1))
    rw [circularChannel_negative, canonicalColorReflection_rootMinus]
    rw [← circularChannel_positive, sheetReflection_negative]
    rfl

/-! The genuine multiplicative colour cycle is the step-two rotation of the
six-label carrier.  The raw step-one hexagon rotation is deliberately not
identified with an algebra automorphism. -/

theorem canonicalColorCycle_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalColorCycle (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.rotation 2 n) := by
  change canonicalColorCycle (circularChannel (zmodIndex.symm n)) =
    cyclotomicChannel
      (InfoGeometry.Canonical.D6SixModeAction.rotation 2 n)
  rw [canonicalColorCycle_circularChannel,
    cyclotomicChannel_rotation_two]

/-! The native orientation-corrected reflection is the shifted reflection on
the cyclic six-label readout. -/

theorem canonicalColorReflection_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalColorReflection (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3) := by
  change canonicalColorReflection (circularChannel (zmodIndex.symm n)) =
    cyclotomicChannel
      (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3)
  rw [canonicalColorReflection_circularChannel,
    cyclotomicChannel_reflection_shifted]

theorem canonicalColorCycle_cyclotomicChannel_mul
    (m n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalColorCycle (cyclotomicChannel m * cyclotomicChannel n) =
      cyclotomicChannel
          (InfoGeometry.Canonical.D6SixModeAction.rotation 2 m) *
        cyclotomicChannel
          (InfoGeometry.Canonical.D6SixModeAction.rotation 2 n) := by
  rw [canonicalColorCycle_map_mul,
    canonicalColorCycle_cyclotomicChannel,
    canonicalColorCycle_cyclotomicChannel]

theorem canonicalColorReflection_cyclotomicChannel_mul
    (m n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalColorReflection (cyclotomicChannel m * cyclotomicChannel n) =
      cyclotomicChannel
          (InfoGeometry.Canonical.D6SixModeAction.reflection m + 3) *
        cyclotomicChannel
          (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3) := by
  rw [canonicalColorReflection_map_mul,
    canonicalColorReflection_cyclotomicChannel,
    canonicalColorReflection_cyclotomicChannel]

/-! The shifted reflection conjugates the native step-two colour cycle to its
inverse on the six-label cyclic readout.  This is the concrete Coxeter
relation seen by the actual circular Zorn channels. -/

theorem cyclotomic_shiftedReflection_conjugates_stepTwoRotation
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    InfoGeometry.Canonical.D6SixModeAction.reflection
          (InfoGeometry.Canonical.D6SixModeAction.rotation 2
            (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3)) + 3 =
      InfoGeometry.Canonical.D6SixModeAction.rotation 4 n := by
  fin_cases n <;> native_decide

theorem cyclotomic_stepTwoRotation_twice
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    InfoGeometry.Canonical.D6SixModeAction.rotation 4 n =
      InfoGeometry.Canonical.D6SixModeAction.rotation 2
        (InfoGeometry.Canonical.D6SixModeAction.rotation 2 n) := by
  fin_cases n <;> native_decide

theorem canonicalColorReflection_cyclotomic_conjugation
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalColorReflection
        (canonicalColorCycle
          (canonicalColorReflection (cyclotomicChannel n))) =
      canonicalColorCycle
        (canonicalColorCycle (cyclotomicChannel n)) := by
  calc
    canonicalColorReflection
        (canonicalColorCycle
          (canonicalColorReflection (cyclotomicChannel n))) =
        canonicalColorReflection
          (canonicalColorCycle
            (cyclotomicChannel
              (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3))) := by
      rw [canonicalColorReflection_cyclotomicChannel]
    _ = canonicalColorReflection
          (cyclotomicChannel
            (InfoGeometry.Canonical.D6SixModeAction.rotation 2
              (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3))) := by
      rw [canonicalColorCycle_cyclotomicChannel]
    _ = cyclotomicChannel
          (InfoGeometry.Canonical.D6SixModeAction.reflection
            (InfoGeometry.Canonical.D6SixModeAction.rotation 2
              (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3)) + 3) := by
      rw [canonicalColorReflection_cyclotomicChannel]
    _ = cyclotomicChannel
          (InfoGeometry.Canonical.D6SixModeAction.rotation 4 n) := by
      rw [cyclotomic_shiftedReflection_conjugates_stepTwoRotation]
    _ = canonicalColorCycle
          (canonicalColorCycle (cyclotomicChannel n)) := by
      rw [canonicalColorCycle_cyclotomicChannel,
        canonicalColorCycle_cyclotomicChannel,
        ← cyclotomic_stepTwoRotation_twice]

theorem canonicalDihedralAction_r_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction (.r 1) (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.rotation 2 n) := by
  rw [canonicalDihedralAction_r]
  exact canonicalColorCycle_cyclotomicChannel n

theorem canonicalDihedralAction_sr_zero_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction (.sr 0) (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.reflection n + 3) := by
  rw [canonicalDihedralAction_sr_zero]
  exact canonicalColorReflection_cyclotomicChannel n

theorem canonicalDihedralAction_r_zero_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction (.r 0) (cyclotomicChannel n) =
      cyclotomicChannel n := by
  have h : (.r 0 : DihedralGroup 3) = 1 := by rfl
  rw [h]
  simp

theorem canonicalDihedralAction_r_two_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction (.r 2) (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.rotation 4 n) := by
  have h : (.r 2 : DihedralGroup 3) = (.r 1) * (.r 1) := by
    simp only [DihedralGroup.r_mul_r]
    native_decide
  rw [h]
  change canonicalDihedralAction (.r 1)
      (canonicalDihedralAction (.r 1) (cyclotomicChannel n)) = _
  rw [canonicalDihedralAction_r_cyclotomicChannel,
    canonicalDihedralAction_r_cyclotomicChannel]
  congr 1
  simp [InfoGeometry.Canonical.D6SixModeAction.rotation]
  abel

theorem canonicalDihedralAction_sr_one_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction (.sr 1) (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.reflection
          (InfoGeometry.Canonical.D6SixModeAction.rotation 2 n) + 3) := by
  have h : (.sr 1 : DihedralGroup 3) = (.sr 0) * (.r 1) := by
    simp only [DihedralGroup.sr_mul_r]
    native_decide
  rw [h]
  change canonicalDihedralAction (.sr 0)
      (canonicalDihedralAction (.r 1) (cyclotomicChannel n)) = _
  rw [canonicalDihedralAction_r_cyclotomicChannel,
    canonicalDihedralAction_sr_zero_cyclotomicChannel]

theorem canonicalDihedralAction_sr_two_cyclotomicChannel
    (n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction (.sr 2) (cyclotomicChannel n) =
      cyclotomicChannel
        (InfoGeometry.Canonical.D6SixModeAction.reflection
          (InfoGeometry.Canonical.D6SixModeAction.rotation 4 n) + 3) := by
  have h : (.sr 2 : DihedralGroup 3) = (.sr 0) * (.r 2) := by
    simp only [DihedralGroup.sr_mul_r]
    native_decide
  rw [h]
  change canonicalDihedralAction (.sr 0)
      (canonicalDihedralAction (.r 2) (cyclotomicChannel n)) = _
  rw [canonicalDihedralAction_r_two_cyclotomicChannel,
    canonicalDihedralAction_sr_zero_cyclotomicChannel]

theorem canonicalDihedralAction_cyclotomicChannel_mul
    (g : DihedralGroup 3)
    (m n : InfoGeometry.Canonical.D6SixModeAction.D6Index) :
    canonicalDihedralAction g
        (cyclotomicChannel m * cyclotomicChannel n) =
      canonicalDihedralAction g (cyclotomicChannel m) *
        canonicalDihedralAction g (cyclotomicChannel n) := by
  exact (canonicalDihedralAction g).map_mul _ _

/-! The native order-six automorphism action reads back to the actual
hexagon-label reindexings on the two generators. -/

theorem canonicalDihedralAction_r_circularChannel (n : HexIndex) :
    canonicalDihedralAction (.r 1) (circularChannel n) =
      circularChannel (colorRotation n) := by
  rw [canonicalDihedralAction_r]
  exact canonicalColorCycle_circularChannel n

theorem canonicalDihedralAction_sr_zero_circularChannel (n : HexIndex) :
    canonicalDihedralAction (.sr 0) (circularChannel n) =
      circularChannel (sheetReflection n) := by
  rw [canonicalDihedralAction_sr_zero]
  exact canonicalColorReflection_circularChannel n

/-! The diagonal Peirce units complete the basis-level readout. -/

@[simp] theorem canonicalColorCycle_zornPlus :
    canonicalColorCycle (zornPlus (R := ℝ)) = zornPlus (R := ℝ) := by
  have h := cartesianZorn_rootPlus_mul_rootMinus 0
  calc
    canonicalColorCycle (zornPlus (R := ℝ)) =
        canonicalColorCycle (cartesianZornLinearEquiv (rootPlus 0) *
          cartesianZornLinearEquiv (rootMinus 0)) := by rw [h]
    _ = cartesianZornLinearEquiv (rootPlus (nextColor 0)) *
          cartesianZornLinearEquiv (rootMinus (nextColor 0)) := by
      rw [canonicalColorCycle_map_mul, canonicalColorCycle_rootPlus,
        canonicalColorCycle_rootMinus]
    _ = zornPlus (R := ℝ) := cartesianZorn_rootPlus_mul_rootMinus (nextColor 0)

@[simp] theorem canonicalColorCycle_zornMinus :
    canonicalColorCycle (zornMinus (R := ℝ)) = zornMinus (R := ℝ) := by
  have h := cartesianZorn_rootMinus_mul_rootPlus 0
  calc
    canonicalColorCycle (zornMinus (R := ℝ)) =
        canonicalColorCycle (cartesianZornLinearEquiv (rootMinus 0) *
          cartesianZornLinearEquiv (rootPlus 0)) := by rw [h]
    _ = cartesianZornLinearEquiv (rootMinus (nextColor 0)) *
          cartesianZornLinearEquiv (rootPlus (nextColor 0)) := by
      rw [canonicalColorCycle_map_mul, canonicalColorCycle_rootMinus,
        canonicalColorCycle_rootPlus]
    _ = zornMinus (R := ℝ) := cartesianZorn_rootMinus_mul_rootPlus (nextColor 0)

@[simp] theorem canonicalColorReflection_zornPlus :
    canonicalColorReflection (zornPlus (R := ℝ)) = zornMinus (R := ℝ) := by
  rw [← cartesianZorn_rootPlus_mul_rootMinus 0,
    canonicalColorReflection_map_mul, canonicalColorReflection_rootPlus,
    canonicalColorReflection_rootMinus,
    cartesianZorn_rootMinus_mul_rootPlus]

@[simp] theorem canonicalColorReflection_zornMinus :
    canonicalColorReflection (zornMinus (R := ℝ)) = zornPlus (R := ℝ) := by
  rw [← cartesianZorn_rootMinus_mul_rootPlus 0,
    canonicalColorReflection_map_mul, canonicalColorReflection_rootMinus,
    canonicalColorReflection_rootPlus,
    cartesianZorn_rootPlus_mul_rootMinus]

theorem canonicalColorCycle_circularFrame (i : Fin 8) :
    canonicalColorCycle (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (circularFrame (cycleFrameIndex i)) := by
  fin_cases i
  · change canonicalColorCycle (cartesianZornLinearEquiv scalarPlus) =
      cartesianZornLinearEquiv scalarPlus
    rw [cartesianZorn_scalarPlus, canonicalColorCycle_zornPlus]
  · change canonicalColorCycle (cartesianZornLinearEquiv (rootPlus 0)) =
      cartesianZornLinearEquiv (rootPlus 1)
    exact canonicalColorCycle_rootPlus 0
  · change canonicalColorCycle (cartesianZornLinearEquiv (rootPlus 1)) =
      cartesianZornLinearEquiv (rootPlus 2)
    exact canonicalColorCycle_rootPlus 1
  · change canonicalColorCycle (cartesianZornLinearEquiv (rootPlus 2)) =
      cartesianZornLinearEquiv (rootPlus 0)
    exact canonicalColorCycle_rootPlus 2
  · change canonicalColorCycle (cartesianZornLinearEquiv scalarMinus) =
      cartesianZornLinearEquiv scalarMinus
    rw [cartesianZorn_scalarMinus, canonicalColorCycle_zornMinus]
  · change canonicalColorCycle (cartesianZornLinearEquiv (rootMinus 0)) =
      cartesianZornLinearEquiv (rootMinus 1)
    exact canonicalColorCycle_rootMinus 0
  · change canonicalColorCycle (cartesianZornLinearEquiv (rootMinus 1)) =
      cartesianZornLinearEquiv (rootMinus 2)
    exact canonicalColorCycle_rootMinus 1
  · change canonicalColorCycle (cartesianZornLinearEquiv (rootMinus 2)) =
      cartesianZornLinearEquiv (rootMinus 0)
    exact canonicalColorCycle_rootMinus 2

theorem canonicalColorReflection_circularFrame (i : Fin 8) :
    canonicalColorReflection (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (circularFrame (reflectionFrameIndex i)) := by
  fin_cases i
  · change canonicalColorReflection (cartesianZornLinearEquiv scalarPlus) =
      cartesianZornLinearEquiv scalarMinus
    rw [cartesianZorn_scalarPlus, canonicalColorReflection_zornPlus,
      cartesianZorn_scalarMinus]
  · change canonicalColorReflection (cartesianZornLinearEquiv (rootPlus 0)) =
      cartesianZornLinearEquiv (rootMinus 0)
    exact canonicalColorReflection_rootPlus 0
  · change canonicalColorReflection (cartesianZornLinearEquiv (rootPlus 1)) =
      cartesianZornLinearEquiv (rootMinus 2)
    exact canonicalColorReflection_rootPlus 1
  · change canonicalColorReflection (cartesianZornLinearEquiv (rootPlus 2)) =
      cartesianZornLinearEquiv (rootMinus 1)
    exact canonicalColorReflection_rootPlus 2
  · change canonicalColorReflection (cartesianZornLinearEquiv scalarMinus) =
      cartesianZornLinearEquiv scalarPlus
    rw [cartesianZorn_scalarMinus, canonicalColorReflection_zornMinus,
      cartesianZorn_scalarPlus]
  · change canonicalColorReflection (cartesianZornLinearEquiv (rootMinus 0)) =
      cartesianZornLinearEquiv (rootPlus 0)
    exact canonicalColorReflection_rootMinus 0
  · change canonicalColorReflection (cartesianZornLinearEquiv (rootMinus 1)) =
      cartesianZornLinearEquiv (rootPlus 2)
    exact canonicalColorReflection_rootMinus 1
  · change canonicalColorReflection (cartesianZornLinearEquiv (rootMinus 2)) =
      cartesianZornLinearEquiv (rootPlus 1)
    exact canonicalColorReflection_rootMinus 2

theorem canonicalDihedralAction_r_circularFrame (i : Fin 8) :
    canonicalDihedralAction (.r 1)
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (circularFrame (cycleFrameIndex i)) := by
  rw [canonicalDihedralAction_r]
  exact canonicalColorCycle_circularFrame i

theorem canonicalDihedralAction_sr_zero_circularFrame (i : Fin 8) :
    canonicalDihedralAction (.sr 0)
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (circularFrame (reflectionFrameIndex i)) := by
  rw [canonicalDihedralAction_sr_zero]
  exact canonicalColorReflection_circularFrame i

theorem canonicalDihedralAction_r_zero_circularFrame (i : Fin 8) :
    canonicalDihedralAction (.r 0)
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (circularFrame i) := by
  have h : (.r 0 : DihedralGroup 3) = 1 := by rfl
  rw [h]
  simp [canonicalDihedralAction, canonicalChiralMulEquiv,
    canonicalChiralLinearEquiv]

theorem canonicalDihedralAction_r_two_circularFrame (i : Fin 8) :
    canonicalDihedralAction (.r 2)
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv
        (circularFrame (cycleFrameIndex (cycleFrameIndex i))) := by
  have h : (.r 2 : DihedralGroup 3) = (.r 1) * (.r 1) := by
    simp only [DihedralGroup.r_mul_r]
    native_decide
  rw [h]
  change canonicalDihedralAction (.r 1)
      (canonicalDihedralAction (.r 1)
        (cartesianZornLinearEquiv (circularFrame i))) =
      cartesianZornLinearEquiv
        (circularFrame (cycleFrameIndex (cycleFrameIndex i)))
  rw [canonicalDihedralAction_r_circularFrame,
    canonicalDihedralAction_r_circularFrame]

theorem canonicalDihedralAction_sr_one_circularFrame (i : Fin 8) :
    canonicalDihedralAction (.sr 1)
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv
        (circularFrame (reflectionFrameIndex (cycleFrameIndex i))) := by
  have h : (.sr 1 : DihedralGroup 3) = (.sr 0) * (.r 1) := by
    simp only [DihedralGroup.sr_mul_r]
    native_decide
  rw [h]
  change canonicalDihedralAction (.sr 0)
      (canonicalDihedralAction (.r 1)
        (cartesianZornLinearEquiv (circularFrame i))) = _
  rw [canonicalDihedralAction_r_circularFrame,
    canonicalDihedralAction_sr_zero_circularFrame]

theorem canonicalDihedralAction_sr_two_circularFrame (i : Fin 8) :
    canonicalDihedralAction (.sr 2)
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv
        (circularFrame (reflectionFrameIndex
          (cycleFrameIndex (cycleFrameIndex i)))) := by
  have h : (.sr 2 : DihedralGroup 3) = (.sr 0) * (.r 2) := by
    simp only [DihedralGroup.sr_mul_r]
    native_decide
  rw [h]
  change canonicalDihedralAction (.sr 0)
      (canonicalDihedralAction (.r 2)
        (cartesianZornLinearEquiv (circularFrame i))) = _
  rw [canonicalDihedralAction_r_two_circularFrame,
    canonicalDihedralAction_sr_zero_circularFrame]

/-- The frame permutation induced by every element of the native finite
dihedral automorphism action.  This is a readout of the six concrete
automorphisms, not an identification of the unsigned order-twelve hexagon
action with algebra automorphisms. -/
def canonicalDihedralFrameIndex : DihedralGroup 3 → Fin 8 → Fin 8
  | .r 0 => fun i => i
  | .r 1 => cycleFrameIndex
  | .r 2 => fun i => cycleFrameIndex (cycleFrameIndex i)
  | .sr 0 => reflectionFrameIndex
  | .sr 1 => fun i => reflectionFrameIndex (cycleFrameIndex i)
  | .sr 2 => fun i =>
      reflectionFrameIndex (cycleFrameIndex (cycleFrameIndex i))

theorem canonicalDihedralAction_circularFrame (g : DihedralGroup 3) (i : Fin 8) :
    canonicalDihedralAction g
        (cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (circularFrame (canonicalDihedralFrameIndex g i)) := by
  fin_cases g
  · exact canonicalDihedralAction_r_zero_circularFrame i
  · exact canonicalDihedralAction_r_circularFrame i
  · exact canonicalDihedralAction_r_two_circularFrame i
  · exact canonicalDihedralAction_sr_zero_circularFrame i
  · exact canonicalDihedralAction_sr_one_circularFrame i
  · exact canonicalDihedralAction_sr_two_circularFrame i

theorem canonicalColorCycle_circularFrame_mul (i j : Fin 8) :
    canonicalColorCycle
        (cartesianZornLinearEquiv (circularFrame i) *
          cartesianZornLinearEquiv (circularFrame j)) =
      cartesianZornLinearEquiv (circularFrame (cycleFrameIndex i)) *
        cartesianZornLinearEquiv (circularFrame (cycleFrameIndex j)) := by
  rw [canonicalColorCycle_map_mul, canonicalColorCycle_circularFrame,
    canonicalColorCycle_circularFrame]

theorem canonicalColorReflection_circularFrame_mul (i j : Fin 8) :
    canonicalColorReflection
        (cartesianZornLinearEquiv (circularFrame i) *
          cartesianZornLinearEquiv (circularFrame j)) =
      cartesianZornLinearEquiv (circularFrame (reflectionFrameIndex i)) *
        cartesianZornLinearEquiv (circularFrame (reflectionFrameIndex j)) := by
  rw [canonicalColorReflection_map_mul, canonicalColorReflection_circularFrame,
    canonicalColorReflection_circularFrame]

end InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction
