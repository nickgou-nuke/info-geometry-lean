import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.AmplituhedronBostConnesBridge
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem

/-!
# Finite Klein-coordinate readout

This module supplies the six-coordinate polynomial carrier used by the
two-row-minor readout in `GrandUnification.AmplituhedronTwistorPluckerDictionary`.
Its Klein-null predicate is only the equation
`p12 * p34 - p13 * p24 + p14 * p23 = 0`; it is not a Minkowski mass shell,
an amplituhedron membership predicate, or a coadjoint Casimir assertion.

The former `amplituhedron_metriplectic_second_law` declaration merely restated
the real-number implication `rev = 0`, `0 ≤ metric`, and
`total = rev + metric` imply `0 ≤ total`. It contained no Plücker point,
coadjoint orbit, or entropy dynamics and had no callers, so it did not establish
a bridge and is intentionally not retained under a misleading name. The actual
conditional coadjoint-orbit second-law theorem is owned by
`SouriauCoadjointOrbitMetriplecticTheorem`; no theorem identifying it with the
Klein equation is claimed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.AmplituhedronMetriplecticBridge

open InfoGeometry.Canonical.AmplituhedronBostConnesBridge
open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

variable {R : Type*} [CommRing R]

/-- Amplituhedron kinematic phase space point -/
structure KinematicPluckerPoint (R : Type*) where
  p12 : R
  p34 : R
  p13 : R
  p24 : R
  p14 : R
  p23 : R

/-- Plücker / Klein Quadric functional -/
def kleinQuadricEval (p : KinematicPluckerPoint R) : R :=
  p.p12 * p.p34 - p.p13 * p.p24 + p.p14 * p.p23

/-- A Plücker-coordinate point is Klein-null when the Klein form vanishes. -/
def IsKleinNull (p : KinematicPluckerPoint R) : Prop :=
  kleinQuadricEval p = 0

/-- Klein-nullity follows from the equivalent coordinate factorization equation. -/
theorem klein_null_of_factorization (p : KinematicPluckerPoint R)
    (h : p.p12 * p.p34 = p.p13 * p.p24 - p.p14 * p.p23) :
    IsKleinNull p := by
  dsimp [IsKleinNull, kleinQuadricEval]
  rw [h]
  ring

/-- The elementary scalar-rate implication formerly presented as an
amplituhedron second law.  This is only real addition and order: it asserts
that a zero reversible rate plus a nonnegative metric rate gives a
nonnegative total rate.  It carries no Plücker, orbit, or dynamics data. -/
theorem totalRate_nonnegative_of_zero_reversible_and_nonnegative_metric
    (revEntropyRate metricEntropyRate totalEntropyRate : ℝ)
    (h_rev : revEntropyRate = 0)
    (h_metric : 0 ≤ metricEntropyRate)
    (h_split : totalEntropyRate = revEntropyRate + metricEntropyRate) :
    0 ≤ totalEntropyRate := by
  rw [h_split, h_rev, zero_add]
  exact h_metric

end InfoGeometry.Canonical.AmplituhedronMetriplecticBridge
