import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.End

/-!
# Canonical Zorn derivation one-parameter group

This module packages the additive flow identities for canonical Zorn
derivations, parameterized by the repository-owned `canonicalZornDerivations`
Lie subalgebra.
-/

namespace InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential

variable (D : canonicalZornDerivations)

/-- Pointwise one-parameter group law for a canonical Zorn derivation. -/
theorem zornFlow_add_apply
    (s t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowLinearEquiv D.1 (s + t) X =
      zornFlowLinearEquiv D.1 s
        (zornFlowLinearEquiv D.1 t X) := by
  exact zornFlowLinearEquiv_add_apply D.1 s t X

/-- Negative time of the Zorn flow inverts the positive-time flow. -/
@[simp]
theorem zornFlow_apply_neg_flow
    (t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowLinearEquiv D.1 t
        (zornFlowLinearEquiv D.1 (-t) X) =
      X := by
  rw [← zornFlowLinearEquiv_add_apply, add_neg_cancel, zornFlowLinearEquiv_zero_apply]

/-- Negative time followed by positive time is identity. -/
@[simp]
theorem zornFlow_neg_flow_apply
    (t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowLinearEquiv D.1 (-t)
        (zornFlowLinearEquiv D.1 t X) =
      X := by
  rw [← zornFlowLinearEquiv_add_apply, neg_add_cancel, zornFlowLinearEquiv_zero_apply]

end InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
