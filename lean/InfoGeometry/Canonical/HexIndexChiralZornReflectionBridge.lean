import InfoGeometry.Canonical.ChiralZornFiniteSymmetry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HexagonalSixRootTiling
import InfoGeometry.Canonical.HexIndexSplitOctonionBridge
import InfoGeometry.Canonical.NonAbelianDihedralSymmetry12

/-!
# Hexagonal labels on the native chiral Zorn carrier

The hexagonal sheet reflection is realized here on the existing
`Physics.Octonion.ChiralZornMatrix` carrier.  This is intentionally a separate
readout from the canonical `ZornMatrix` coordinates: the theorem transports
the already-owned native `rotateMulEquiv`/`reflectMulEquiv` actions and does
not identify the two carriers by notation.
-/

namespace InfoGeometry.Canonical.HexIndexChiralZornReflectionBridge

open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Physics.Octonion
open InfoGeometry.Physics.Octonion.ChiralZornMatrix

noncomputable section

def chiralChannel (s : Fin 2) (c : Fin 3) : ChiralZornMatrix ℚ :=
  if s = 0 then
    { n_plus := 0
      n_minus := 0
      sigma_plus := Pi.single c 1
      sigma_minus := 0 }
  else
    { n_plus := 0
      n_minus := 0
      sigma_plus := 0
      sigma_minus := Pi.single c 1 }

def hexChiralChannel (n : HexIndex) : ChiralZornMatrix ℚ :=
  let p := sheetColorEquiv n
  chiralChannel (hexSheetFin2 p.1) p.2

@[simp] theorem hexChiralChannel_eq (n : HexIndex) :
    hexChiralChannel n =
      chiralChannel (hexSheetFin2 (sheetColorEquiv n).1)
        (sheetColorEquiv n).2 := by
  rfl

theorem hexChiralChannel_injective :
    Function.Injective hexChiralChannel := by
  intro m n h
  fin_cases m <;> fin_cases n <;>
    simp [hexChiralChannel, chiralChannel, sheetColorEquiv,
      sheetOf, colorOf, hexSheetFin2] at h ⊢
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2

theorem reflect_chiralChannel (s : Fin 2) (c : Fin 3) :
    reflectMulEquiv (chiralChannel s c) =
      chiralChannel (1 - s) (reflectColor c) := by
  apply ChiralZornMatrix.ext
  · fin_cases s <;> simp [chiralChannel, reflectMulEquiv_apply, reflect]
  · fin_cases s <;> simp [chiralChannel, reflectMulEquiv_apply, reflect]
  · funext d
    fin_cases s <;> fin_cases c <;> fin_cases d <;>
      simp [chiralChannel, reflectMulEquiv_apply, reflect,
        reflectColor, Pi.single_apply]
  · funext d
    fin_cases s <;> fin_cases c <;> fin_cases d <;>
      simp [chiralChannel, reflectMulEquiv_apply, reflect,
        reflectColor, Pi.single_apply]

theorem rotate_chiralChannel (s : Fin 2) (c : Fin 3) :
    rotateMulEquiv (chiralChannel s c) =
      chiralChannel s (nextColor c) := by
  apply ChiralZornMatrix.ext
  · fin_cases s <;> fin_cases c <;>
      simp [chiralChannel, rotateMulEquiv_apply, rotateColor]
  · fin_cases s <;> fin_cases c <;>
      simp [chiralChannel, rotateMulEquiv_apply, rotateColor]
  · funext d
    fin_cases s <;> fin_cases c <;> fin_cases d <;>
      simp [chiralChannel, rotateMulEquiv_apply, rotateColor,
        nextColor, prevColor, Pi.single_apply]
  · funext d
    fin_cases s <;> fin_cases c <;> fin_cases d <;>
      simp [chiralChannel, rotateMulEquiv_apply, rotateColor,
        nextColor, prevColor, Pi.single_apply]

theorem reflect_hexChiralChannel (n : HexIndex) :
    reflectMulEquiv (hexChiralChannel n) =
      hexChiralChannel (sheetReflection n) := by
  fin_cases n <;>
    simp only [hexChiralChannel_eq]
  all_goals rw [reflect_chiralChannel]
  all_goals simp [sheetColorEquiv, sheetOf, colorOf, sheetReflection, hexSheetFin2,
    reflectColor]

theorem reflect_hexChiralChannel_involutive (n : HexIndex) :
    reflectMulEquiv (reflectMulEquiv (hexChiralChannel n)) =
      hexChiralChannel n := by
  rw [reflect_hexChiralChannel, reflect_hexChiralChannel,
    sheetReflection_involutive]

theorem rotate_hexChiralChannel (n : HexIndex) :
    rotateMulEquiv (hexChiralChannel n) =
      hexChiralChannel (colorRotation n) := by
  fin_cases n <;>
    simp only [hexChiralChannel_eq]
  all_goals rw [rotate_chiralChannel]
  all_goals congr 1

theorem rotate_hexChiralChannel_three (n : HexIndex) :
    rotateMulEquiv (rotateMulEquiv (rotateMulEquiv (hexChiralChannel n))) =
      hexChiralChannel n := by
  rw [rotate_hexChiralChannel, rotate_hexChiralChannel,
    rotate_hexChiralChannel, colorRotation_cube]

theorem rotate_hexChiralChannel_mul (m n : HexIndex) :
    rotateMulEquiv (hexChiralChannel m * hexChiralChannel n) =
      hexChiralChannel (colorRotation m) * hexChiralChannel (colorRotation n) := by
  rw [map_mul, rotate_hexChiralChannel, rotate_hexChiralChannel]

theorem reflect_hexChiralChannel_mul (m n : HexIndex) :
    reflectMulEquiv (hexChiralChannel m * hexChiralChannel n) =
      hexChiralChannel (sheetReflection m) * hexChiralChannel (sheetReflection n) := by
  rw [map_mul, reflect_hexChiralChannel, reflect_hexChiralChannel]

theorem reflect_rotate_reflect_hexChiralChannel (n : HexIndex) :
    reflectMulEquiv (rotateMulEquiv (reflectMulEquiv (hexChiralChannel n))) =
      hexChiralChannel (colorRotation (colorRotation n)) := by
  calc
    reflectMulEquiv (rotateMulEquiv (reflectMulEquiv (hexChiralChannel n))) =
        rotateMulEquiv (rotateMulEquiv (hexChiralChannel n)) :=
      reflectMulEquiv_rotateMulEquiv_reflectMulEquiv_apply _
    _ = hexChiralChannel (colorRotation (colorRotation n)) := by
      rw [rotate_hexChiralChannel, rotate_hexChiralChannel]

def hexRotationPower (i : ZMod 3) (n : HexIndex) : HexIndex :=
  match i.val with
  | 0 => n
  | 1 => colorRotation n
  | _ => colorRotation (colorRotation n)

theorem dihedralAction_r_hexChiralChannel (i : ZMod 3) (n : HexIndex) :
    dihedralAction (.r i) (hexChiralChannel n) =
      hexChiralChannel (hexRotationPower i n) := by
  fin_cases i
  · change (1 : ChiralZornMatrix ℚ ≃* ChiralZornMatrix ℚ) (hexChiralChannel n) = _
    simp [hexRotationPower]
  · change rotateMulEquiv (hexChiralChannel n) = _
    rw [rotate_hexChiralChannel]
    rfl
  · change (rotateMulEquiv ^ 2) (hexChiralChannel n) = _
    rw [show (rotateMulEquiv ^ 2) (hexChiralChannel n) =
      rotateMulEquiv (rotateMulEquiv (hexChiralChannel n)) by rfl]
    rw [rotate_hexChiralChannel, rotate_hexChiralChannel]
    rfl

theorem dihedralAction_sr_hexChiralChannel (i : ZMod 3) (n : HexIndex) :
    dihedralAction (.sr i) (hexChiralChannel n) =
      hexChiralChannel (sheetReflection (hexRotationPower i n)) := by
  fin_cases i
  · change reflectMulEquiv (hexChiralChannel n) = _
    rw [reflect_hexChiralChannel]
    rfl
  · change reflectMulEquiv (rotateMulEquiv (hexChiralChannel n)) = _
    rw [rotate_hexChiralChannel, reflect_hexChiralChannel]
    rfl
  · change reflectMulEquiv (rotateMulEquiv (rotateMulEquiv (hexChiralChannel n))) = _
    rw [rotate_hexChiralChannel, rotate_hexChiralChannel,
      reflect_hexChiralChannel]
    rfl

theorem rotate_hexChiralChannel_positive (c : HexColor) :
    rotateMulEquiv (hexChiralChannel (positiveVertex c)) =
      hexChiralChannel (colorRotation (positiveVertex c)) := by
  rw [colorRotation_positive]
  fin_cases c <;>
    simp only [hexChiralChannel_eq]
  all_goals rw [rotate_chiralChannel]
  all_goals congr 1

theorem rotate_hexChiralChannel_negative (c : HexColor) :
    rotateMulEquiv (hexChiralChannel (negativeVertex c)) =
      hexChiralChannel (colorRotation (negativeVertex c)) := by
  rw [colorRotation_negative]
  fin_cases c <;>
    simp only [hexChiralChannel_eq]
  all_goals rw [rotate_chiralChannel]
  all_goals congr 1

end
end InfoGeometry.Canonical.HexIndexChiralZornReflectionBridge
