import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Compactly supported complex decomposition

AFP's complex Riesz representation proof reduces a positive complex functional
to a real positive functional by composing with `complex_of_real`, then
reconstructs the complex statement by splitting a compactly supported complex
function into real and imaginary parts.

This file exposes exactly that Lean-native `C_c` decomposition layer.
-/

open scoped CompactlySupported

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ComplexDecomposition

variable {X : Type*} [TopologicalSpace X]

/-- Real part as a bundled continuous map. -/
def complexReContinuousMap : C(ℂ, ℝ) where
  toFun := Complex.re
  continuous_toFun := Complex.continuous_re

/-- Imaginary part as a bundled continuous map. -/
def complexImContinuousMap : C(ℂ, ℝ) where
  toFun := Complex.im
  continuous_toFun := Complex.continuous_im

/-- Inclusion of real numbers into complex numbers as a bundled continuous map. -/
def complexOfRealContinuousMap : C(ℝ, ℂ) where
  toFun := fun x => (x : ℂ)
  continuous_toFun := Complex.continuous_ofReal

/-- Real part of a compactly supported complex-valued continuous function. -/
noncomputable def ccRe (f : C_c(X, ℂ)) : C_c(X, ℝ) :=
  f.compLeft complexReContinuousMap

/-- Imaginary part of a compactly supported complex-valued continuous function. -/
noncomputable def ccIm (f : C_c(X, ℂ)) : C_c(X, ℝ) :=
  f.compLeft complexImContinuousMap

/-- Real inclusion of a compactly supported real-valued continuous function. -/
noncomputable def ccOfReal (f : C_c(X, ℝ)) : C_c(X, ℂ) :=
  f.compLeft complexOfRealContinuousMap

@[simp]
theorem complexReContinuousMap_apply (z : ℂ) :
    complexReContinuousMap z = z.re := rfl

@[simp]
theorem complexImContinuousMap_apply (z : ℂ) :
    complexImContinuousMap z = z.im := rfl

@[simp]
theorem complexOfRealContinuousMap_apply (x : ℝ) :
    complexOfRealContinuousMap x = (x : ℂ) := rfl

@[simp]
theorem ccRe_apply (f : C_c(X, ℂ)) (x : X) :
    ccRe f x = (f x).re := by
  exact CompactlySupportedContinuousMap.compLeft_apply rfl f x

@[simp]
theorem ccIm_apply (f : C_c(X, ℂ)) (x : X) :
    ccIm f x = (f x).im := by
  exact CompactlySupportedContinuousMap.compLeft_apply rfl f x

@[simp]
theorem ccOfReal_apply (f : C_c(X, ℝ)) (x : X) :
    ccOfReal f x = (f x : ℂ) := by
  exact CompactlySupportedContinuousMap.compLeft_apply rfl f x

@[simp]
theorem ccRe_ccOfReal (f : C_c(X, ℝ)) :
    ccRe (ccOfReal f) = f := by
  ext x
  simp [ccRe_apply, ccOfReal_apply]

@[simp]
theorem ccIm_ccOfReal (f : C_c(X, ℝ)) :
    ccIm (ccOfReal f) = 0 := by
  ext x
  simp [ccIm_apply, ccOfReal_apply]

/--
Pointwise reconstruction of a compactly supported complex-valued continuous
function from its real and imaginary parts.
-/
@[simp]
theorem ccOfReal_re_add_I_smul_ccOfReal_im (f : C_c(X, ℂ)) :
    ccOfReal (ccRe f) + Complex.I • ccOfReal (ccIm f) = f := by
  ext x
  simp [Complex.ext_iff]

end ComplexDecomposition
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
