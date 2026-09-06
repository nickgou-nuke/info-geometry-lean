import InfoGeometry.Clifford.ModularCftBridge
import Mathlib.Tactic

noncomputable section

/-!
# DiscreteMoebiusGroup

Projective readout of the LCFT parabolic monodromy as a fractional linear
transformation.  The matrix identities from `ModularCftBridge` become literal
translations on the affine chart where the denominator is `1`.
-/

namespace InfoGeometry.Clifford.DiscreteMoebiusGroup

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter
open InfoGeometry.Clifford.ModularCftBridge

/-- Fractional linear action of a `2 × 2` complex matrix on the affine chart. -/
def moebiusAction (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)

/-- The standard modular `T` generator acts as `z ↦ z + 1`. -/
theorem moebius_T_action (z : ℂ) :
    moebiusAction modularT z = z + 1 := by
  simp [moebiusAction, modularT]

/-- The `m`th modular `T` power acts as translation by `m`. -/
theorem moebius_T_pow_action (m : ℕ) (z : ℂ) :
    moebiusAction (modularT ^ m) z = z + (m : ℂ) := by
  rw [modularT_pow]
  simp [moebiusAction]

/-- The modular `S` generator acts as inversion `z ↦ -1 / z` on this chart. -/
theorem moebius_S_action (z : ℂ) :
    moebiusAction modularS z = -1 / z := by
  simp [moebiusAction, modularS]

/-- The LCFT parabolic flow acts projectively as `z ↦ z + t`. -/
theorem moebius_monodromy_flow_action (t z : ℂ) :
    moebiusAction (lcftParabolicFlowStep t) z = z + t := by
  simp [moebiusAction, lcftParabolicFlowStep, infinitesimalNullGenerator,
    epsilon, jordanNilpotent]

/-- Repeated LCFT parabolic flow translates by the accumulated parameter. -/
theorem moebius_monodromy_flow_pow_action (t : ℂ) (n : ℕ) (z : ℂ) :
    moebiusAction (lcftParabolicFlowStep t ^ n) z = z + (n : ℂ) * t := by
  rw [lcftParabolicFlow_pow]
  exact moebius_monodromy_flow_action ((n : ℂ) * t) z

/-- Fixed point predicate for the affine projective readout. -/
def IsFixedPoint (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : Prop :=
  moebiusAction M z = z

/-- The lower endpoint of the affine chart is sheared to the flow parameter. -/
theorem monodromy_shearing_at_zero (t : ℂ) :
    moebiusAction (lcftParabolicFlowStep t) 0 = t := by
  simpa using moebius_monodromy_flow_action t 0

/-- One Hadjiivanov wrap acts projectively as a translation by `logShearBase`. -/
theorem moebius_hadjiivanov_unscaled_action (z : ℂ) :
    moebiusAction (lcftParabolicFlowStep logShearBase) z = z + logShearBase := by
  exact moebius_monodromy_flow_action logShearBase z

end InfoGeometry.Clifford.DiscreteMoebiusGroup
