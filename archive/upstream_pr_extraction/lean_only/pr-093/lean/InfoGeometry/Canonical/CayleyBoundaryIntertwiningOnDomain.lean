import Mathlib
import InfoGeometry.Canonical.CayleyBoundaryContinuity

namespace InfoGeometry.Canonical

open InfoGeometry.Topology

/-!
The Cayley chart intertwines the real hyperbolic dilation with the disk
Möbius map on the domain where the latter denominator is nonzero.  Keeping
the pole property explicit avoids silently turning a fractional-linear map
into a globally regular map.
-/

def cayleyIntertwiningDomain (s : ℝ) : Set ℝ :=
  {x | (diskBoostParameter s : ℂ) * cayleyBoundary x + 1 ≠ 0}

lemma cayley_fractional_linear_identity
    (a z : ℂ)
    (ha : a + 1 ≠ 0)
    (hz : z + Complex.I ≠ 0)
    (hleft : a * z + Complex.I ≠ 0)
    (hden : ((a - 1) / (a + 1)) * ((z - Complex.I) / (z + Complex.I)) + 1 ≠ 0) :
    (a * z - Complex.I) / (a * z + Complex.I) =
      (((z - Complex.I) / (z + Complex.I)) + (a - 1) / (a + 1)) /
        (((a - 1) / (a + 1)) * ((z - Complex.I) / (z + Complex.I)) + 1) := by
  apply (div_eq_iff hleft).2
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).2
  field_simp [ha, hz]
  ring

theorem cayleyIntertwiningDomain_iff (s x : ℝ) :
    x ∈ cayleyIntertwiningDomain s ↔
      (diskBoostParameter s : ℂ) * cayleyBoundary x + 1 ≠ 0 :=
  Iff.rfl

theorem cayley_modularBoost_intertwining_on_domain
    (s x : ℝ)
    (hden : (diskBoostParameter s : ℂ) * cayleyBoundary x + 1 ≠ 0) :
    cayleyBoundary (Real.exp (2 * s) * x) =
      diskBoundaryBoost s (cayleyBoundary x) := by
  unfold cayleyBoundary diskBoundaryBoost diskBoostParameter
  have h_exp : (Real.exp (2 * s) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (2 * s)
  have h_exp_add : (Real.exp (2 * s) + 1 : ℂ) ≠ 0 := by
    exact_mod_cast diskBoostParameter_den_ne_zero s
  have h_cayley : ((x : ℂ) + Complex.I) ≠ 0 := by
    exact cayleyBoundary_den_ne_zero x
  have h_cayley_scaled :
      ((Real.exp (2 * s) * x : ℝ) : ℂ) + Complex.I ≠ 0 := by
    exact InfoGeometry.Topology.cayleyBoundary_den_ne_zero (Real.exp (2 * s) * x)
  have h_q :
      (((Real.exp (2 * s) - 1) / (Real.exp (2 * s) + 1) : ℝ) : ℂ) *
          (((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)) + 1 ≠ 0 := by
    exact hden
  have hmain := cayley_fractional_linear_identity
    (a := (Real.exp (2 * s) : ℂ))
    (z := (x : ℂ))
    h_exp_add h_cayley (by
      simpa only [Complex.ofReal_mul] using h_cayley_scaled) (by
        simpa [div_eq_mul_inv] using h_q)
  simpa using hmain

theorem cayley_modularBoost_intertwining_on_domain'
    (s x : ℝ)
    (hx : x ∈ cayleyIntertwiningDomain s) :
    cayleyBoundary (Real.exp (2 * s) * x) =
      diskBoundaryBoost s (cayleyBoundary x) :=
  cayley_modularBoost_intertwining_on_domain s x hx

end InfoGeometry.Canonical
