import Mathlib.Tactic
import InfoGeometry.Twistor.PenroseTwistor

/-!
# Chiral sheets of the Penrose twistor carrier

The Penrose carrier is a pair of two-component complex spinors.  This file
records that decomposition and its chosen real `(1 + 3)` and `(3 + 1)`
coordinate readouts.  It does not identify these coordinate carriers with a
Zorn product or impose a reality condition on a bi-twistor.
-/

noncomputable section

namespace InfoGeometry.Twistor.ChiralTwistorSheets

open InfoGeometry.Twistor.PenroseTwistor

abbrev TwistorPlus := Fin 2 → ℂ
abbrev TwistorMinus := Fin 2 → ℂ
abbrev PeircePlus4 := ℝ × (Fin 3 → ℝ)
abbrev PeirceMinus4 := (Fin 3 → ℝ) × ℝ

noncomputable def twistorChiralDecomposition :
    TwistorCarrier ≃ₗ[ℂ] TwistorPlus × TwistorMinus where
  toFun z := (fun i => z i, fun i => z (i + 2))
  invFun p := fun i => if h : i.val < 2 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 2, by omega⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨p, q⟩
    apply Prod.ext <;> funext i <;> simp
  map_add' := by
    intro z w
    apply Prod.ext <;> funext i <;> simp
  map_smul' := by
    intro c z
    apply Prod.ext <;> funext i <;> simp

@[simp] theorem twistorChiralDecomposition_apply (z : TwistorCarrier) :
    twistorChiralDecomposition z = (fun i => z i, fun i => z (i + 2)) := rfl

noncomputable def twistorPlusRealEquiv :
    TwistorPlus ≃ₗ[ℝ] PeircePlus4 where
  toFun z := ((z 0).re, ![(z 0).im, (z 1).re, (z 1).im])
  invFun p := fun i => if i = 0 then ⟨p.1, p.2 0⟩ else ⟨p.2 1, p.2 2⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> apply Complex.ext <;> simp
  right_inv := by
    rintro ⟨a, v⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  map_add' := by
    intro z w
    apply Prod.ext <;> funext i <;> simp
  map_smul' := by
    intro r z
    apply Prod.ext <;> funext i <;> simp

noncomputable def twistorMinusRealEquiv :
    TwistorMinus ≃ₗ[ℝ] PeirceMinus4 where
  toFun z := (![(z 0).re, (z 0).im, (z 1).re], (z 1).im)
  invFun p := fun i => if i = 0 then ⟨p.1 0, p.1 1⟩ else ⟨p.1 2, p.2⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> apply Complex.ext <;> simp
  right_inv := by
    rintro ⟨v, b⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' := by
    intro z w
    apply Prod.ext <;> funext i <;> simp
  map_smul' := by
    intro r z
    apply Prod.ext <;> funext i <;> simp

end InfoGeometry.Twistor.ChiralTwistorSheets
