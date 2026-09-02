import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential

namespace InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz

noncomputable section

open InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential

def scalarPotential (sigma t : ℝ) : ℝ :=
  InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential.masterPotential sigma t

def scaleA (sigma t : ℝ) : ℝ := sigma * (1 - sigma) + t ^ 2

def scaleB (sigma t : ℝ) : ℝ := (1 - 2 * sigma) * t

def dilationField (sigma t : ℝ) : ℝ × ℝ := (-scaleA sigma t, -scaleB sigma t)

def quarterTurn (v : ℝ × ℝ) : ℝ × ℝ := (v.2, -v.1)

def rotationalField (sigma t : ℝ) : ℝ × ℝ :=
  quarterTurn (dilationField sigma t)

def unifiedField (gamma sigma t : ℝ) : ℝ × ℝ :=
  (-gamma * scaleA sigma t - scaleB sigma t,
    -gamma * scaleB sigma t + scaleA sigma t)

theorem scalarPotential_centralLeaf (t : ℝ) :
    scalarPotential (1 / 2) t = 0 := by
  simpa [scalarPotential] using
    (masterPotential_eq_zero_on_criticalLine t)

theorem scaleA_centered (sigma t : ℝ) :
    scaleA sigma t = 1 / 4 - (sigma - 1 / 2) ^ 2 + t ^ 2 := by
  unfold scaleA
  ring

theorem scaleB_centered (sigma t : ℝ) :
    scaleB sigma t = -2 * (sigma - 1 / 2) * t := by
  unfold scaleB
  ring

theorem quarterTurn_sq (v : ℝ × ℝ) :
    quarterTurn (quarterTurn v) = (-v.1, -v.2) := by
  cases v
  rfl

theorem rotationalField_eq_quarterTurn (sigma t : ℝ) :
    rotationalField sigma t = quarterTurn (dilationField sigma t) := by
  rfl

theorem potential_unitary_orthogonal (sigma t : ℝ) :
    (dilationField sigma t).1 * (rotationalField sigma t).1 +
      (dilationField sigma t).2 * (rotationalField sigma t).2 = 0 := by
  unfold rotationalField quarterTurn dilationField
  ring

theorem unifiedField_eq_sum (gamma sigma t : ℝ) :
    unifiedField gamma sigma t =
      (gamma * (dilationField sigma t).1 + (rotationalField sigma t).1,
       gamma * (dilationField sigma t).2 + (rotationalField sigma t).2) := by
  unfold unifiedField rotationalField quarterTurn dilationField
  ext <;> simp <;> ring

end

end InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz
