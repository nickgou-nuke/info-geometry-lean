import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Complex vector-space adapters for AFP `Complex_Vector_Spaces0`

AFP's `Complex_Vector_Spaces0` builds a complex scalar hierarchy, complex-linear
maps, complex span, and scalar simplification lemmas from Isabelle/HOL
foundations.

In Lean/mathlib these are native structures:

* `NormedSpace ℂ E`;
* `ContinuousLinearMap`;
* `Submodule.span ℂ`;
* restriction of scalars from `ℂ` to `ℝ`.

This file exposes only thin adapter lemmas needed by the complex bounded
operator corridor.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ComplexVectorSpaces

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ## Complex scalar decomposition -/

/--
Decompose complex scalar multiplication into real and imaginary real-scalar
parts.

This is the Lean-native analogue of the AFP scalar decomposition lemmas based
on `scaleR_scaleC` and `re_add_im`.
-/
theorem complex_smul_re_im (z : ℂ) (x : E) :
    z • x = (z.re : ℝ) • x + (z.im : ℝ) • ((Complex.I : ℂ) • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul]
  congr 1

theorem neg_one_smul (x : E) :
    ((-1 : ℂ) • x) = -x := by
  simp

theorem two_smul_apply (x : E) :
    ((2 : ℂ) • x) = x + x := by
  rw [two_smul]

theorem half_smul_double (x : E) :
    ((1 / 2 : ℂ) • (x + x)) = x := by
  rw [← two_smul (R := ℂ)]
  rw [← mul_smul]
  norm_num

/-! ## Complex-linear maps as real-linear maps -/

/-- Restrict a bounded complex-linear map to a bounded real-linear map. -/
def restrictScalarsReal (T : E →L[ℂ] F) : E →L[ℝ] F :=
  T.restrictScalars ℝ

@[simp]
theorem restrictScalarsReal_apply (T : E →L[ℂ] F) (x : E) :
    restrictScalarsReal T x = T x :=
  rfl

@[simp]
theorem norm_restrictScalarsReal (T : E →L[ℂ] F) :
    ‖restrictScalarsReal T‖ = ‖T‖ :=
  ContinuousLinearMap.norm_restrictScalars T

/-! ## Complex span adapters -/

/-- Membership in a one-dimensional complex span. -/
theorem mem_complex_span_singleton_iff (x y : E) :
    y ∈ Submodule.span ℂ ({x} : Set E) ↔ ∃ c : ℂ, c • x = y := by
  simpa using (Submodule.mem_span_singleton (R := ℂ) (x := y) (y := x))

theorem mem_complex_span_singleton_self (x : E) :
    x ∈ Submodule.span ℂ ({x} : Set E) :=
  Submodule.mem_span_singleton_self x

end ComplexVectorSpaces
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
