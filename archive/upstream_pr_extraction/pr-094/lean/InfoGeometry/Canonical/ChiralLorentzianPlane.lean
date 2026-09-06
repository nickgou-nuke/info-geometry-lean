import Mathlib
import InfoGeometry.Canonical.ThreeColorIntegralMultiplicationTable

namespace InfoGeometry.Canonical

/-!
  Coordinate geometry of the red chiral plane.  This file deliberately
  separates the quadratic form from the split-octonion product: it proves
  the Lorentzian coordinate model, not a physical spacetime identification.
-/

def chiralPlaneVector (a b : ℤ) : StandardIntegralSplitOctonion :=
  a • iOct + b • ilOct

def chiralPlaneQuadratic (a b : ℤ) : ℤ :=
  a ^ 2 - b ^ 2

theorem chiralPlaneVector_mem_red (a b : ℤ) :
    chiralPlaneVector a b ∈ Pr := by
  rw [chiralPlaneVector]
  exact Pr.add_mem
    (Pr.smul_mem _ (Submodule.subset_span (by simp)))
    (Pr.smul_mem _ (Submodule.subset_span (by simp)))

theorem chiralPlaneQuadratic_plus_null (a : ℤ) :
    chiralPlaneQuadratic a a = 0 := by
  simp [chiralPlaneQuadratic]

theorem chiralPlaneQuadratic_minus_null (a : ℤ) :
    chiralPlaneQuadratic a (-a) = 0 := by
  simp [chiralPlaneQuadratic]

theorem redNullPlus_eq_chiralPlaneVector :
    nr_plus = chiralPlaneVector 1 1 := by
  simp [chiralPlaneVector, nr_plus]

theorem redNullMinus_eq_chiralPlaneVector :
    nr_minus = chiralPlaneVector 1 (-1) := by
  simp [chiralPlaneVector, nr_minus, sub_eq_add_neg]

theorem redNullPlus_is_quadratically_null :
    chiralPlaneQuadratic 1 1 = 0 :=
  chiralPlaneQuadratic_plus_null 1

theorem redNullMinus_is_quadratically_null :
    chiralPlaneQuadratic 1 (-1) = 0 :=
  chiralPlaneQuadratic_minus_null 1

theorem chiralPlane_quadratic_factorization (a b : ℤ) :
    chiralPlaneQuadratic a b = (a - b) * (a + b) := by
  dsimp [chiralPlaneQuadratic]
  ring

end InfoGeometry.Canonical
