/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveParityReadout

/-! Concrete scope checks for the arbitrary-ring parity/readout owner.
These are regression instances, not models substituted for its carrier. -/
namespace InfoGeometry.Canonical.ReflexiveParityRegression

open DeBruijnRotorAlternationCycle GrassmannianBundleCyclotomicOrientability

/-- Native matrix units with a nonzero complementary sector. -/
def d3 : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def b3 : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

lemma seed3_pair : IsDualSeedPair d3 b3 := by
  constructor <;> decide +kernel

/-- The completion is essential when the active support is proper. -/
theorem proper_support_ambient_reflection :
    carrierSupport d3 b3 ≠ 1 ∧
    (ambientReflectionUnit seed3_pair.d_sq seed3_pair.B_sq seed3_pair.dBd seed3_pair.BdB :
      Matrix (Fin 3) (Fin 3) ℤ) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  decide +kernel

/-- A genuinely mixed element need not be either fixed or negated by reflection. -/
theorem mixed_element_nonzero_defect :
    let X := transitionVelocity d3 b3 + wheelGenerator d3 b3
    let U := ambientReflectionUnit seed3_pair.d_sq seed3_pair.B_sq seed3_pair.dBd seed3_pair.BdB
    unitOrbitMap X U = (2 : ℤ) • b3 ∧
    unitOrbitMap X U ≠ X ∧ unitOrbitMap X U ≠ -X := by
  decide +kernel

/-- An algebraic nonzero polarized readout, without a state-normalization claim. -/
theorem polarized_readout_five :
    Matrix.trace (phasePolarization d3 b3 *
      InfoGeometry.Core.PeirceDensityIntertwining.density d3 b3 (4 : ℤ) 9) = 5 := by
  decide +kernel

/-- Self-adjointness is not a normalization law. -/
theorem selfAdjoint_not_involutive :
    star (2 : ℤ) = 2 ∧ (2 : ℤ) * 2 ≠ 1 := by decide +kernel

namespace CharacteristicTwo
local instance : StarRing (ZMod 2) := starRingOfComm

def d : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
def b : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]

lemma seed_pair : IsDualSeedPair d b := by
  constructor <;> decide +kernel

/-- Nonzero coefficients and noncommuting adjoint seeds do not force a nonzero defect. -/
theorem mixed_element_can_vanish :
    d * b ≠ b * d ∧ star d = b ∧
    (1 : ZMod 2) ≠ 0 ∧ transitionVelocity d b ≠ 0 ∧ wheelGenerator d b ≠ 0 ∧
    (1 : ZMod 2) • transitionVelocity d b + (1 : ZMod 2) • wheelGenerator d b = 0 := by
  decide +kernel

end CharacteristicTwo
end InfoGeometry.Canonical.ReflexiveParityRegression
