import Mathlib.Tactic
import InfoGeometry.Canonical.BinaryModularMoebiusBridge

namespace InfoGeometry.Canonical.ModularTheory

open Real
open StrictBinaryState

namespace StrictBinaryState

variable (pi p : StrictBinaryState)

/-- Psi_{p|pi}(s) -/
noncomputable def relativeModularGeneratingFunction (s : ℝ) : ℝ :=
  log (pi.prob * (deltaPlus pi p) ^ s + 
       (1 - pi.prob) * (deltaMinus pi p) ^ s)

theorem relativeModularGeneratingFunction_eq (s : ℝ) :
    relativeModularGeneratingFunction pi p s = 
    log ((p.prob ^ s) * (pi.prob ^ (1 - s)) + 
         ((1 - p.prob) ^ s) * ((1 - pi.prob) ^ (1 - s))) := by
  dsimp [relativeModularGeneratingFunction, deltaPlus, deltaMinus]
  have ha_pos : 0 < pi.prob := pi.h_pos
  have hr_pos : 0 < p.prob := p.h_pos
  have ha_sub_pos : 0 < 1 - pi.prob := sub_pos_of_lt pi.h_lt_one
  have hr_sub_pos : 0 < 1 - p.prob := sub_pos_of_lt p.h_lt_one
  have h1 : pi.prob * (p.prob / pi.prob) ^ s = p.prob ^ s * pi.prob ^ (1 - s) := by
    rw [div_rpow hr_pos.le ha_pos.le, rpow_sub ha_pos, rpow_one]
    ring
  have h2 : (1 - pi.prob) * ((1 - p.prob) / (1 - pi.prob)) ^ s = (1 - p.prob) ^ s * (1 - pi.prob) ^ (1 - s) := by
    rw [div_rpow hr_sub_pos.le ha_sub_pos.le, rpow_sub ha_sub_pos, rpow_one]
    ring
  rw [h1, h2]

/-- Petz-Rényi divergence D_s^P(p | pi) -/
noncomputable def petzRenyiDivergence (s : ℝ) (hs : s ≠ 1) : ℝ :=
  (relativeModularGeneratingFunction pi p s) / (s - 1)

theorem petzRenyiDivergence_eq_standard (s : ℝ) (_hs : s ≠ 1) :
    petzRenyiDivergence pi p s _hs = 
    (1 / (s - 1)) * log ((p.prob ^ s) * (pi.prob ^ (1 - s)) + 
                         ((1 - p.prob) ^ s) * ((1 - pi.prob) ^ (1 - s))) := by
  dsimp [petzRenyiDivergence]
  rw [relativeModularGeneratingFunction_eq pi p s]
  ring

end StrictBinaryState

end InfoGeometry.Canonical.ModularTheory
