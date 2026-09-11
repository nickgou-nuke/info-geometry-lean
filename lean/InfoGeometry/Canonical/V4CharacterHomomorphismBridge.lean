import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.V4O55SouriauChernPartitionBridge

/-!
# Native finite-group characters for the `V₄` partition readout

The partition owner stores the four signs as scalar evaluations.  This file
bundles the same signs as genuine homomorphisms into the multiplicative units
of `ℝ`.  The source is `Multiplicative ZetaKlein4` because
`ZetaKlein4 = ZMod 2 × ZMod 2` carries its Klein-group law additively.

No thermodynamic trace, Gibbs state, or Souriau realization is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.V4CharacterHomomorphismBridge

open InfoGeometry.Canonical.V4O55SouriauChernPartition
open InfoGeometry.Topology.ZetaFlowKleinSemidirect

def characterUnit : V4Char → ZetaKlein4 → ℝˣ
  | V4Char.chi0, _ => 1
  | V4Char.chih, (0, 0) => 1
  | V4Char.chih, (0, 1) => 1
  | V4Char.chih, (1, 0) => -1
  | V4Char.chih, (1, 1) => -1
  | V4Char.chiu, (0, 0) => 1
  | V4Char.chiu, (0, 1) => -1
  | V4Char.chiu, (1, 0) => -1
  | V4Char.chiu, (1, 1) => 1
  | V4Char.chis, (0, 0) => 1
  | V4Char.chis, (0, 1) => -1
  | V4Char.chis, (1, 0) => 1
  | V4Char.chis, (1, 1) => -1

@[simp] theorem characterUnit_coe (χ : V4Char) (g : ZetaKlein4) :
    (characterUnit χ g : ℝ) = V4Char.eval χ g := by
  cases χ <;> rcases g with ⟨g₁, g₂⟩ <;>
    fin_cases g₁ <;> fin_cases g₂ <;> rfl

def spatialCharacter (g : ZetaKlein4) : ℝ :=
  if g.2 = 0 then 1 else -1

theorem spatialCharacter_mul (g h : ZetaKlein4) :
    spatialCharacter (g + h) = spatialCharacter g * spatialCharacter h := by
  have h_scalar : ∀ a b : ZMod 2,
      (if (a + b) = 0 then (1 : ℝ) else -1) =
      (if a = 0 then 1 else -1) * (if b = 0 then 1 else -1) := by
    intro a b
    fin_cases a <;> fin_cases b
    · simp
    · simp
    · simp
    · have h : (1 : ZMod 2) + 1 = 0 := rfl
      simp [h]
  exact h_scalar g.2 h.2

theorem characterEval_chih (g : ZetaKlein4) :
    V4Char.eval V4Char.chih g =
      ZetaKlein4.heightCharacter g := by
  rcases g with ⟨g₁, g₂⟩
  fin_cases g₁ <;> fin_cases g₂ <;> rfl

theorem characterEval_chis (g : ZetaKlein4) :
    V4Char.eval V4Char.chis g = spatialCharacter g := by
  rcases g with ⟨g₁, g₂⟩
  fin_cases g₁ <;> fin_cases g₂ <;> rfl

theorem characterEval_chiu (g : ZetaKlein4) :
    V4Char.eval V4Char.chiu g =
      ZetaKlein4.heightCharacter g * spatialCharacter g := by
  rcases g with ⟨g₁, g₂⟩
  fin_cases g₁ <;> fin_cases g₂ <;>
    simp [V4Char.eval, ZetaKlein4.heightCharacter, spatialCharacter]

theorem characterEval_product (χ : V4Char) (g h : ZetaKlein4) :
    V4Char.eval χ (g + h) =
      V4Char.eval χ g * V4Char.eval χ h := by
  cases χ
  · simp [V4Char.eval]
  · rw [characterEval_chih, characterEval_chih, characterEval_chih]
    exact ZetaKlein4.heightCharacter_mul g h
  · rw [characterEval_chiu, characterEval_chiu, characterEval_chiu,
      ZetaKlein4.heightCharacter_mul, spatialCharacter_mul]
    ring
  · rw [characterEval_chis, characterEval_chis, characterEval_chis]
    exact spatialCharacter_mul g h

theorem characterUnit_product (χ : V4Char) (g h : ZetaKlein4) :
    characterUnit χ (g + h) = characterUnit χ g * characterUnit χ h := by
  apply Units.ext
  change (characterUnit χ (g + h) : ℝ) =
    (characterUnit χ g : ℝ) * (characterUnit χ h : ℝ)
  rw [characterUnit_coe, characterUnit_coe, characterUnit_coe]
  exact characterEval_product χ g h

def characterUnitHom (χ : V4Char) :
    Multiplicative ZetaKlein4 →* ℝˣ where
  toFun g := characterUnit χ (g : ZetaKlein4)
  map_one' := by
    change characterUnit χ (0, 0) = 1
    cases χ <;> rfl
  map_mul' := by
    intro g h
    change characterUnit χ (Multiplicative.toAdd g + Multiplicative.toAdd h) =
      characterUnit χ (Multiplicative.toAdd g) *
        characterUnit χ (Multiplicative.toAdd h)
    exact characterUnit_product χ (Multiplicative.toAdd g) (Multiplicative.toAdd h)

@[simp] theorem characterUnitHom_coe (χ : V4Char) (g : ZetaKlein4) :
    (characterUnitHom χ (Multiplicative.ofAdd g) : ℝ) =
      V4Char.eval χ g := by
  exact characterUnit_coe χ g

theorem chiu_eval_eq_chih_mul_chis (g : ZetaKlein4) :
    V4Char.eval V4Char.chiu g =
      V4Char.eval V4Char.chih g * V4Char.eval V4Char.chis g := by
  rw [characterEval_chiu, characterEval_chih, characterEval_chis]

theorem chiu_characterUnit_eq_product (g : ZetaKlein4) :
    characterUnit V4Char.chiu g =
      characterUnit V4Char.chih g * characterUnit V4Char.chis g := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [characterUnit_coe, characterUnit_coe, characterUnit_coe]
  exact chiu_eval_eq_chih_mul_chis g

end InfoGeometry.Canonical.V4CharacterHomomorphismBridge
