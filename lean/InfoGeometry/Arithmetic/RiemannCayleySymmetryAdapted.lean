/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-! Symmetry-adapted centered coordinates for the Riemann Cayley chart. -/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannCayleySymmetryAdapted

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

def centeredComplexCoordinate (s : ℂ) : ℂ := s - 1 / 2

theorem centeredComplexCoordinate_add_half (s : ℂ) :
    centeredComplexCoordinate s + 1 / 2 = s := by
  unfold centeredComplexCoordinate
  ring

@[simp] theorem centeredComplexCoordinate_one_sub (s : ℂ) :
    centeredComplexCoordinate (1 - s) = -centeredComplexCoordinate s := by
  unfold centeredComplexCoordinate
  ring

theorem cayley_conjugates_functionalReflection_to_inv
    (s : ℂ) :
    cayleyToFugacity (functionalReflection s) =
      (cayleyToFugacity s)⁻¹ := by
  simpa [functionalReflection] using cayleyToFugacity_one_sub_eq_inv s

theorem criticalLine_iff_cayley_normSq_one (s : ℂ) :
    CriticalLine s ↔ Complex.normSq (cayleyToFugacity s) = 1 := by
  change OnCriticalLine s ↔ OnLeeYangCircle (cayleyToFugacity s)
  exact criticalLine_iff_cayley_unitCircle s

theorem riemannXiCayley_symmetry_adapted
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    riemannXiCayley z⁻¹ = riemannXiCayley z := by
  exact riemannXiCayley_inv_eq hz hz'

theorem riemannZeta_zero_iff_symmetry_adapted_cayley_zero
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannZeta s = 0 ↔ riemannXiCayley (cayleyToFugacity s) = 0 := by
  exact riemannXiCayley_zero_iff_riemannZeta_zero_of_strip hRe hRe'

end InfoGeometry.Arithmetic.RiemannCayleySymmetryAdapted
