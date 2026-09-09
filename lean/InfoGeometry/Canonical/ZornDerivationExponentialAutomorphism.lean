import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
import Mathlib.Tactic

/-!
# Zorn Derivation Exponential Automorphism

This module establishes the canonical owner for the exponentiated derivation flow
on the split-octonionic Zorn matrix algebra.

## Core Structure & Theorems:
1. **Generic Exponential Flow Laws**:
   - `expDerivation_zero`: $\Phi_0 = \mathrm{id}_{\mathbb{O}_s}$.
   - `expDerivation_add`: $\Phi_{s+t} = \Phi_s \circ \Phi_t$.
   - `expDerivation_mul`: $\Phi_t(X \circ Y) = \Phi_t(X) \circ \Phi_t(Y)$.
   - `expDerivation_one`: $\Phi_1$ is a multiplicative automorphism.
   - `expDerivation_inv`: $\Phi_{-t} \circ \Phi_t = \mathrm{id}$.
2. **Determinant and Composition Norm Invariance**:
   - `expDerivation_preserves_detZ`: $\det Z(\Phi_t X) = \det Z(X)$.
3. **One-Parameter Group Homomorphism**:
   - `expDerivation_groupHom`: group homomorphism $\text{Multiplicative } \mathbb{R} \to^* \operatorname{Aut}(\mathbb{O}_s)$.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornDerivationExponentialAutomorphism

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

variable (D : canonicalZornDerivations)

/-- 🏆 THEOREM 1: Time-zero flow is the identity automorphism. -/
theorem expDerivation_zero (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowMulEquiv D 0 X = X :=
  zornFlowMulEquiv_zero_apply D X

/-- 🏆 THEOREM 2: 1-parameter group composition law: exp((s+t)D) = exp(sD) ∘ exp(tD). -/
theorem expDerivation_add (s t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowMulEquiv D (s + t) X =
      zornFlowMulEquiv D s (zornFlowMulEquiv D t X) :=
  zornFlowMulEquiv_add_apply D s t X

/-- 🏆 THEOREM 3: Exponentiated derivation preserves non-associative Zorn multiplication. -/
theorem expDerivation_mul (t : ℝ)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowMulEquiv D t (X * Y) =
      zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y :=
  (zornFlowMulEquiv D t).map_mul X Y

/-- 🏆 THEOREM 4: Time-one exponential automorphism. -/
theorem expDerivation_one
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornDerivationExpAutomorphism D (X * Y) =
      zornDerivationExpAutomorphism D X * zornDerivationExpAutomorphism D Y :=
  zornDerivationExpAutomorphism_map_mul D X Y

/-- 🏆 THEOREM 5: Inverse flow is given by the negative derivation generator. -/
theorem expDerivation_inv (D : canonicalZornDerivations) (t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowLinearEquiv (-D.1) t (zornFlowLinearEquiv D.1 t X) = X :=
  zornFlowLinearEquiv_neg_apply D.1 t X

/-- 🏆 THEOREM 6: Reverse inverse identity. -/
theorem expDerivation_inv_rev (D : canonicalZornDerivations) (t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    zornFlowLinearEquiv D.1 t (zornFlowLinearEquiv (-D.1) t X) = X :=
  zornFlowLinearEquiv_apply_neg D.1 t X

/-- 🏆 THEOREM 7: Derivation exponential preserves the split-octonion determinant / composition norm. -/
theorem expDerivation_preserves_detZ (t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    InfoGeometry.Canonical.ZornMatrix.detZ (zornFlowLinearEquiv D.1 t X) =
      InfoGeometry.Canonical.ZornMatrix.detZ X := by
  exact InfoGeometry.Canonical.RealSplitOctonionAut.preserves_detZ
    (InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t) X

/-- 🏆 THEOREM 8: The canonical derivation flow as a group homomorphism into RealSplitOctonionAut. -/
noncomputable def expDerivation_groupHom :
    Multiplicative ℝ →* InfoGeometry.Canonical.RealSplitOctonionAut :=
  InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAutGroupHom D

@[simp]
theorem expDerivation_groupHom_apply (t : ℝ) :
    expDerivation_groupHom D (Multiplicative.ofAdd t) =
      InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t := rfl

end InfoGeometry.Canonical.ZornDerivationExponentialAutomorphism

end noncomputable section
