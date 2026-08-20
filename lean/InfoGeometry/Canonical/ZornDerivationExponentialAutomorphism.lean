import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
import Mathlib.Tactic

/-!
# Zorn Derivation Exponential Automorphism

This module provides the generic automorphism properties for the canonical
Zorn derivation exponential, packaging the five core one-parameter group and
multiplicativity theorems for split-octonion automorphisms.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornDerivationExponentialAutomorphism

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

variable (D : canonicalZornDerivations)

/-- 🏆 THEOREM 1: Time-zero flow is the identity automorphism. -/
@[simp]
theorem expDerivation_zero (X : CZ) :
    zornFlowMulEquiv D 0 X = X :=
  zornFlowMulEquiv_zero_apply D X

/-- 🏆 THEOREM 2: 1-parameter group composition law: exp((s+t)D) = exp(sD) ∘ exp(tD). -/
theorem expDerivation_add (s t : ℝ) (X : CZ) :
    zornFlowMulEquiv D (s + t) X =
      zornFlowMulEquiv D s (zornFlowMulEquiv D t X) :=
  zornFlowMulEquiv_add_apply D s t X

/-- 🏆 THEOREM 3: Exponentiated derivation preserves non-associative Zorn multiplication. -/
theorem expDerivation_mul (t : ℝ) (X Y : CZ) :
    zornFlowMulEquiv D t (X * Y) =
      zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y :=
  (zornFlowMulEquiv D t).map_mul X Y

/-- 🏆 THEOREM 4: Time-one exponential automorphism. -/
theorem expDerivation_one (X Y : CZ) :
    zornDerivationExpAutomorphism D (X * Y) =
      zornDerivationExpAutomorphism D X * zornDerivationExpAutomorphism D Y :=
  zornDerivationExpAutomorphism_map_mul D X Y

/-- 🏆 THEOREM 5: Inverse flow is given by the negative derivation generator. -/
@[simp]
theorem expDerivation_inv (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv (-D.1) t (zornFlowLinearEquiv D.1 t X) = X :=
  zornFlowLinearEquiv_neg_apply D.1 t X

end InfoGeometry.Canonical.ZornDerivationExponentialAutomorphism

end noncomputable section