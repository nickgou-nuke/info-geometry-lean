import InfoGeometry.Canonical.ZornFiniteVectorCalculus
import InfoGeometry.Canonical.ZornMaxwellComponentReadout
import Mathlib.Tactic

/-!
# Differential bridge for the Zorn Maxwell component readout

This owner instantiates the finite component packet from the existing
`DifferentialCarrier`.  The source terms are induced from the fields, while
the homogeneous laws are proved from curl-gradient, divergence-curl, and an
explicit time/space commutation hypothesis.  No source dynamics or
differential-form Yang--Mills contract is supplied.
-/

namespace InfoGeometry.Canonical.ZornMaxwellDifferentialBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornFiniteVectorCalculus
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout
open InfoGeometry.Canonical.ZornMaxwellComponentReadout

local notation "Vec3" => ZornVec3 ℝ

def timeNeg (D : DifferentialCarrier (R := ℝ)) (x : ℝ) : Prop :=
  D.timeDerivative (-x) = -D.timeDerivative x

def inducedComponents
    (D : DifferentialCarrier (R := ℝ))
    (scalar : ℝ) (vector : Vec3) : MaxwellComponents where
  rho := divergence D (electricReadout (potentialData D scalar vector))
  current := fun i =>
    curl D (magneticReadout (potentialData D scalar vector)) i -
      D.timeDerivative (electricReadout (potentialData D scalar vector) i)
  divE := divergence D (electricReadout (potentialData D scalar vector))
  divB := divergence D (magneticReadout (potentialData D scalar vector))
  dtE := fun i => D.timeDerivative (electricReadout (potentialData D scalar vector) i)
  dtB := fun i => D.timeDerivative (magneticReadout (potentialData D scalar vector) i)
  curlE := curl D (electricReadout (potentialData D scalar vector))
  curlB := curl D (magneticReadout (potentialData D scalar vector))

theorem inducedComponents_divB_zero
    (D : DifferentialCarrier (R := ℝ)) (scalar : ℝ) (vector : Vec3) :
    divergence D (magneticReadout (potentialData D scalar vector)) = 0 := by
  exact divergence_curl D vector

theorem curl_time_commute
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (v : Vec3) :
    curl D (fun i => D.timeDerivative (v i)) =
      fun i => D.timeDerivative (curl D v i) := by
  have hsub (x y : ℝ) :
      D.timeDerivative (x - y) =
        D.timeDerivative x - D.timeDerivative y := by
    rw [sub_eq_add_neg, D.time_add, hneg y, sub_eq_add_neg]
  funext i
  fin_cases i <;>
    simp [curl, hcomm, hsub]

theorem inducedComponents_faraday_zero
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) :
    ∀ i, faradayResidual (inducedComponents D scalar vector) i = 0 := by
  have hsub (x y : ℝ) :
      D.timeDerivative (x - y) =
        D.timeDerivative x - D.timeDerivative y := by
    rw [sub_eq_add_neg, D.time_add, hneg y, sub_eq_add_neg]
  intro i
  fin_cases i <;>
    simp [inducedComponents, faradayResidual, electricReadout,
      magneticReadout, potentialData, gradient, curl, hcomm,
      D.time_add, hsub, D.spatial_add, D.spatial_neg,
      D.spatial_commute]

theorem inducedComponents_maxwellLaws
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : Vec3) :
    MaxwellLaws (inducedComponents D scalar vector) := by
  refine ⟨rfl, inducedComponents_divB_zero D scalar vector, ?_, ?_⟩
  · exact inducedComponents_faraday_zero D hneg hcomm scalar vector
  · intro i
    rfl

end InfoGeometry.Canonical.ZornMaxwellDifferentialBridge
