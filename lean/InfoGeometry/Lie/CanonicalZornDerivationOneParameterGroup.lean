import InfoGeometry.Lie.CanonicalZornDerivationExponential
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
    (X : CZ) :
    zornFlowLinearEquiv D.1 (s + t) X =
      zornFlowLinearEquiv D.1 s
        (zornFlowLinearEquiv D.1 t X) := by
  exact zornFlowLinearEquiv_add_apply D.1 s t X

/-- Negative time of the Zorn flow inverts the positive-time flow. -/
@[simp]
theorem zornFlow_apply_neg_flow
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D.1 t
        (zornFlowLinearEquiv D.1 (-t) X) =
      X := by
  have h := zornFlowLinearEquiv_neg_eq_symm D.1 t
  rw [h]
  exact LinearEquiv.apply_symm_apply (zornFlowLinearEquiv D.1 t) X

end InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
