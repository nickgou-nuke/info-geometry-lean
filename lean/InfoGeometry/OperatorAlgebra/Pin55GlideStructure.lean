import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Two-generator integer-matrix Clifford core

This module proves the relations for two explicit `32 × 32` integer matrices:
one generator squares to `+1`, the other to `-1`, and they anticommute. The
carrier is `ℤ^32`, not a real spinor space, and this file does not construct the
other eight generators or prove the full `Cl(5,5)` representation.

It is the Lean twin of `tools/sympy/pin55_glide_reflections.py`.

The concrete matrices below prove:

* `γ_space² = 1`;
* `γ_time² = -1`;
* `γ_space γ_time = - γ_time γ_space`;
* the glide core `γ_space γ_time` has square `1`;
* `γ_space * (γ_space * γ_time) = γ_time` and the opposite multiplication gives
  the sign-flipped readout.

#### SIGN AUDIT
The separate SymPy computation checks a ten-generator real matrix model and
finds its volume element square `K² = +I₃₂`, not `-I₃₂`. That computation is
not imported as Lean proof evidence; this file establishes only the displayed
two-generator integer-matrix identities.
-/


namespace InfoGeometry.OperatorAlgebra.Pin55

open Matrix

/-- Upper-right `16 × 16` identity block inside a `32 × 32` matrix. -/
def upperRightId32 : InfoGeometry.Algebra.FiniteSpin.Mat32Z :=
  fun i j => if i.val < 16 ∧ j.val = i.val + 16 then 1 else 0

/-- Lower-left `16 × 16` identity block inside a `32 × 32` matrix. -/
def lowerLeftId32 : InfoGeometry.Algebra.FiniteSpin.Mat32Z :=
  fun i j => if 16 ≤ i.val ∧ j.val + 16 = i.val then 1 else 0

/-- Positive-norm Clifford generator, with square `+1`. -/
def gamma_space : InfoGeometry.Algebra.FiniteSpin.Mat32Z := upperRightId32 + lowerLeftId32

/-- Negative-norm Clifford generator, with square `-1`. -/
def gamma_time : InfoGeometry.Algebra.FiniteSpin.Mat32Z := upperRightId32 - lowerLeftId32

/-- The concrete positive-norm spinor generator squares to `+1`. -/
theorem gamma_space_sq : gamma_space * gamma_space = 1 :=
  by native_decide

/-- The concrete negative-norm spinor generator squares to `-1`. -/
theorem gamma_time_sq : gamma_time * gamma_time = -1 :=
  by native_decide

/-- The two concrete spinor generators anticommute. -/
theorem gamma_space_time_anticomm : gamma_space * gamma_time = - (gamma_time * gamma_space) :=
  by native_decide

/-- Even product of the displayed positive- and negative-norm generators. -/
def glideCore : InfoGeometry.Algebra.FiniteSpin.Mat32Z := gamma_space * gamma_time

/-- Left multiplication by `γ_space` collapses the glide core to `γ_time`. -/
theorem glide_left_product_reduces :
    gamma_space * glideCore = gamma_time := by
  unfold glideCore
  rw [← Matrix.mul_assoc, gamma_space_sq, Matrix.one_mul]

/-- Right multiplication by `γ_space` produces the sign-flipped readout. -/
theorem glide_right_product_sign :
    glideCore * gamma_space = -gamma_time := by
  native_decide

/-- The two-reflection glide core squares to `+1` in the finite spinor core. -/
theorem glide_core_sq : glideCore * glideCore = 1 := by
  native_decide

end InfoGeometry.OperatorAlgebra.Pin55
