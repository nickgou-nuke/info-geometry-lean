import InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

/-!
# Coefficient covariance for the hexagonal circular channels

This owner records the exact tensor-level behavior of the two color
reindexings already induced by the hexagon rotation and sheet reflection.
It deliberately stops at the `δ`/`ε` coefficient layer: these identities do
not by themselves construct an algebra automorphism of the canonical Zorn
carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCartanDihedralCoefficients

open InfoGeometry.Canonical
open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

/-- The color permutation induced by one positive hexagon rotation. -/
def rotateColor (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 1) % 3, by omega⟩

/-- The color permutation induced by the sheet reflection. -/
def reflectColor (i : Fin 3) : Fin 3 :=
  ⟨(3 - i.val) % 3, by omega⟩

@[simp] theorem rotateColor_zero : rotateColor 0 = 1 := by decide

@[simp] theorem rotateColor_one : rotateColor 1 = 2 := by decide

@[simp] theorem rotateColor_two : rotateColor 2 = 0 := by decide

@[simp] theorem reflectColor_zero : reflectColor 0 = 0 := by decide

@[simp] theorem reflectColor_one : reflectColor 1 = 2 := by decide

@[simp] theorem reflectColor_two : reflectColor 2 = 1 := by decide

theorem rotateColor_injective : Function.Injective rotateColor := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [rotateColor] at h ⊢

theorem reflectColor_injective : Function.Injective reflectColor := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [reflectColor] at h ⊢

theorem delta_rotate (i j : Fin 3) :
    (if rotateColor i = rotateColor j then (1 : ℝ) else 0) =
      (if i = j then (1 : ℝ) else 0) := by
  by_cases h : i = j
  · subst h
    simp
  · simp [h]
    intro hij
    exact h (rotateColor_injective hij)

theorem delta_reflect (i j : Fin 3) :
    (if reflectColor i = reflectColor j then (1 : ℝ) else 0) =
      (if i = j then (1 : ℝ) else 0) := by
  by_cases h : i = j
  · subst h
    simp
  · simp [h]
    intro hij
    exact h (reflectColor_injective hij)

theorem leviCivita3_rotate (k i j : Fin 3) :
    (leviCivita3 (rotateColor k) (rotateColor i) (rotateColor j) : ℝ) =
      (leviCivita3 k i j : ℝ) := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [rotateColor, leviCivita3]

theorem leviCivita3_reflect (k i j : Fin 3) :
    (leviCivita3 (reflectColor k) (reflectColor i) (reflectColor j) : ℝ) =
      -(leviCivita3 k i j : ℝ) := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [reflectColor, leviCivita3]

end InfoGeometry.Lie.SplitOctonionCartanDihedralCoefficients
