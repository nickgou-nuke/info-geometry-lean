/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic

import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Complex.MobiusApolloniusFoliation

/-!
# Cayley–Apollonius Möbius Conjugacy

The fixed transition map `C z = -(z + 3) / (3z + 1)` identifies the
Riemann–Cayley coordinate `s / (1 - s)` with the midpoint Apollonius map.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyApolloniusConjugacy

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Complex.MobiusApollonius

def cayleyApolloniusTransition (z : ℂ) : ℂ :=
  -(z + 3) / (3 * z + 1)

theorem cayley_transition_denominator
    (s : ℂ) (hs : 1 - s ≠ 0) :
    3 * cayleyToFugacity s + 1 = (2 * s + 1) / (1 - s) := by
  unfold cayleyToFugacity
  field_simp [hs]
  ring

theorem cayley_transition_denominator_ne_zero
    (s : ℂ) (hs : 1 - s ≠ 0) (hp : s + 1 / 2 ≠ 0) :
    3 * cayleyToFugacity s + 1 ≠ 0 := by
  have htwo : 2 * s + 1 ≠ 0 := by
    intro h
    apply hp
    calc
      s + 1 / 2 = (1 / 2 : ℂ) * (2 * s + 1) := by ring
      _ = 0 := by rw [h]; ring
  rw [cayley_transition_denominator s hs]
  exact div_ne_zero htwo hs

theorem mobiusMap_eq_cayleyApolloniusTransition
    (s : ℂ) (hs : 1 - s ≠ 0) (hp : s + 1 / 2 ≠ 0) :
    mobiusMap s = cayleyApolloniusTransition (cayleyToFugacity s) := by
  have hc := cayley_transition_denominator_ne_zero s hs hp
  unfold mobiusMap cayleyApolloniusTransition cayleyToFugacity at *
  field_simp [hs, hp, hc]
  ring

theorem cayleyApolloniusTransition_second_denominator
    (z : ℂ) (hz : 3 * z + 1 ≠ 0) :
    3 * cayleyApolloniusTransition z + 1 = (-8 : ℂ) / (3 * z + 1) := by
  unfold cayleyApolloniusTransition
  field_simp [hz]
  ring

theorem cayleyApolloniusTransition_second_denominator_ne_zero
    (z : ℂ) (hz : 3 * z + 1 ≠ 0) :
    3 * cayleyApolloniusTransition z + 1 ≠ 0 := by
  rw [cayleyApolloniusTransition_second_denominator z hz]
  exact div_ne_zero (by norm_num) hz

end InfoGeometry.Canonical.CayleyApolloniusConjugacy
