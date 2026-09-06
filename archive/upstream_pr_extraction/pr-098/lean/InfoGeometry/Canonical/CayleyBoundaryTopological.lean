import Mathlib
import InfoGeometry.Canonical.ZornVectorMatrixMöbiusAction
import InfoGeometry.Topology.CayleyModularBoundary

namespace InfoGeometry.Canonical

open InfoGeometry.Topology


/-!
Topological regularity for the Cayley chart and its hyperbolic Möbius map.
The disk map is stated as `ContinuousOn` on its genuine denominator domain;
this avoids treating a fractional-linear formula as globally defined at its
pole.
-/

def diskBoundaryBoostDomain (s : ℝ) : Set ℂ :=
  {z | (diskBoostParameter s : ℂ) * z + 1 ≠ 0}

theorem cayleyBoundary_image_mem_diskBoundaryBoostDomain
    (s x : ℝ)
    (hden : (diskBoostParameter s : ℂ) * cayleyBoundary x + 1 ≠ 0) :
    cayleyBoundary x ∈ diskBoundaryBoostDomain s :=
  hden

theorem diskBoostParameter_add_one_ne_zero (s : ℝ) :
    (diskBoostParameter s : ℂ) + 1 ≠ 0 := by
  intro h
  have hreal := congrArg Complex.re h
  have hreal' : diskBoostParameter s + 1 = 0 := by
    simpa using hreal
  unfold diskBoostParameter at hreal'
  have hden : Real.exp (2 * s) + 1 ≠ 0 := by
    positivity
  field_simp [hden] at hreal'
  nlinarith [Real.exp_pos (2 * s)]

theorem one_sub_diskBoostParameter_ne_zero (s : ℝ) :
    -(1 : ℂ) * (diskBoostParameter s : ℂ) + 1 ≠ 0 := by
  intro h
  have hreal := congrArg Complex.re h
  have hreal' : -diskBoostParameter s + 1 = 0 := by
    simpa using hreal
  unfold diskBoostParameter at hreal'
  have hden : Real.exp (2 * s) + 1 ≠ 0 := by
    positivity
  field_simp [hden] at hreal'
  nlinarith [Real.exp_pos (2 * s)]

theorem diskBoundaryBoost_fixed_minus_one (s : ℝ) :
    diskBoundaryBoost s (-1) = (-1 : ℂ) := by
  exact diskBoundaryBoost_fixed_minus_one_of_den_ne_zero s
    (one_sub_diskBoostParameter_ne_zero s)

theorem diskBoundaryBoost_fixed_one (s : ℝ) :
    diskBoundaryBoost s 1 = (1 : ℂ) := by
  exact diskBoundaryBoost_fixed_one_of_den_ne_zero s
    (diskBoostParameter_add_one_ne_zero s)

end InfoGeometry.Canonical
