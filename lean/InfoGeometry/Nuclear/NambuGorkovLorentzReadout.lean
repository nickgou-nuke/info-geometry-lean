/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Nuclear.SplitOctonionNambuGorkovBridge
import InfoGeometry.Recovered.SpacetimeLorentzTransformations

/-!
# Nambu--Gorkov to Lorentz determinant readout

This file supplies the missing typed bridge.  It identifies the negative
Bogoliubov quadratic readout with a restricted Lorentz determinant.  It does
not identify every Bogoliubov transformation with a Lorentz transformation.
-/

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Nuclear.NambuGorkov

namespace InfoGeometry.Nuclear.NambuGorkovLorentz

/-- The restricted spacetime representative of a real Nambu--Gorkov carrier.
The Euclidean length of the pairing vector is placed in the fourth split
coordinate, so its determinant is the negative quasiparticle square. -/
def spacetimeRepresentative (N : NambuGorkovCarrier ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  InfoGeometry.Spacetime.spacetimeMatrix 0 0 N.xi
    (Real.sqrt (Vec3.dot N.delta N.delta))

theorem spacetimeRepresentative_det (N : NambuGorkovCarrier ℝ) :
    (spacetimeRepresentative N).det = - (bogoliubovEnergy N) ^ 2 := by
  rw [spacetimeRepresentative, InfoGeometry.Spacetime.det_spacetimeMatrix]
  have hdot : 0 ≤ Vec3.dot N.delta N.delta := by
    dsimp [Vec3.dot]
    nlinarith [sq_nonneg (N.delta 0), sq_nonneg (N.delta 1),
      sq_nonneg (N.delta 2)]
  have hsum : 0 ≤ N.xi ^ 2 + Vec3.dot N.delta N.delta := by
    positivity
  rw [Real.sq_sqrt hdot]
  rw [bogoliubovEnergy, Real.sq_sqrt hsum]
  ring

/-- The Nambu--Gorkov quadratic readout is invariant under every unit
split-quaternion sandwich acting on its representative. -/
theorem bogoliubovEnergy_sq_lorentz_invariant
    (q : Matrix (Fin 2) (Fin 2) ℝ)
    (N : NambuGorkovCarrier ℝ)
    (hq : q.det = 1) :
    -(InfoGeometry.Spacetime.lorentzTransform q
        (spacetimeRepresentative N)).det =
      (bogoliubovEnergy N) ^ 2 := by
  rw [InfoGeometry.Spacetime.lorentz_isometry q
    (spacetimeRepresentative N) hq]
  rw [spacetimeRepresentative_det]
  ring

end InfoGeometry.Nuclear.NambuGorkovLorentz
