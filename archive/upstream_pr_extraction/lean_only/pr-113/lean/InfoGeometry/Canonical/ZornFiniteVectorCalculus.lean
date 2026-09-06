import InfoGeometry.Canonical.ZornPotentialDifferentialReadout
import Mathlib.Tactic

/-!
# Finite vector-calculus carrier for the Zorn readout

This is the smallest calculus interface needed to distinguish `φ ∇` from
`∇ φ`.  It contains one time derivation, three spatial derivations, their
product rules, and commuting spatial mixed partials.  The standard curl-of-
gradient and divergence-of-curl identities are derived from those laws.
-/

namespace InfoGeometry.Canonical.ZornFiniteVectorCalculus

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout

variable {R : Type*} [CommRing R]

structure DifferentialCarrier where
  timeDerivative : R → R
  spatialDerivative : Fin 3 → R → R
  time_add : ∀ x y, timeDerivative (x + y) = timeDerivative x + timeDerivative y
  time_mul : ∀ x y, timeDerivative (x * y) =
    timeDerivative x * y + x * timeDerivative y
  spatial_add : ∀ i x y, spatialDerivative i (x + y) =
    spatialDerivative i x + spatialDerivative i y
  spatial_neg : ∀ i x, spatialDerivative i (-x) = -spatialDerivative i x
  spatial_mul : ∀ i x y, spatialDerivative i (x * y) =
    spatialDerivative i x * y + x * spatialDerivative i y
  spatial_commute : ∀ i j x,
    spatialDerivative i (spatialDerivative j x) =
      spatialDerivative j (spatialDerivative i x)

def gradient (D : DifferentialCarrier (R := R)) (x : R) : ZornVec3 R :=
  fun i => D.spatialDerivative i x

def divergence (D : DifferentialCarrier (R := R)) (v : ZornVec3 R) : R :=
  ∑ i : Fin 3, D.spatialDerivative i (v i)

def curl (D : DifferentialCarrier (R := R)) (v : ZornVec3 R) : ZornVec3 R :=
  fun i =>
    if i = (0 : Fin 3) then
      D.spatialDerivative 1 (v 2) - D.spatialDerivative 2 (v 1)
    else if i = (1 : Fin 3) then
      D.spatialDerivative 2 (v 0) - D.spatialDerivative 0 (v 2)
    else
      D.spatialDerivative 0 (v 1) - D.spatialDerivative 1 (v 0)

theorem curl_gradient (D : DifferentialCarrier (R := R)) (x : R) :
    curl D (gradient D x) = fun _ => 0 := by
  funext i
  fin_cases i
  · simp [curl, gradient, D.spatial_commute]
  · simp [curl, gradient, D.spatial_commute]
  · simp [curl, gradient, D.spatial_commute]

theorem divergence_curl (D : DifferentialCarrier (R := R)) (v : ZornVec3 R) :
    divergence D (curl D v) = 0 := by
  have hsub (i : Fin 3) (x y : R) :
      D.spatialDerivative i (x - y) =
        D.spatialDerivative i x - D.spatialDerivative i y := by
    calc
      D.spatialDerivative i (x - y) =
          D.spatialDerivative i (x + (-y)) := by rw [sub_eq_add_neg]
      _ = D.spatialDerivative i x + D.spatialDerivative i (-y) :=
        D.spatial_add i x (-y)
      _ = D.spatialDerivative i x - D.spatialDerivative i y := by
        rw [D.spatial_neg]
        exact (sub_eq_add_neg _ _).symm
  simp [divergence, curl, Fin.sum_univ_three, hsub]
  rw [D.spatial_commute 0 1 (v 2), D.spatial_commute 0 2 (v 1),
    D.spatial_commute 1 2 (v 0), D.spatial_commute 1 0 (v 2),
    D.spatial_commute 2 0 (v 1), D.spatial_commute 2 1 (v 0)]
  ring

def potentialData
    (D : DifferentialCarrier (R := R)) (scalar : R) (vector : ZornVec3 R) :
    PotentialDifferentialData (R := R) where
  timePotential := scalar
  scalarPotential := scalar
  spatialPotential := vector
  timePotentialDerivative := D.timeDerivative scalar
  spatialPotentialDerivative := fun i => D.timeDerivative (vector i)
  scalarGradient := gradient D scalar
  potentialDivergence := divergence D vector
  potentialCurl := curl D vector

theorem potentialData_curl_gradient_zero
    (D : DifferentialCarrier (R := R)) (scalar : R) :
    curl D (gradient D scalar) = fun _ => 0 :=
  curl_gradient D scalar

end InfoGeometry.Canonical.ZornFiniteVectorCalculus
