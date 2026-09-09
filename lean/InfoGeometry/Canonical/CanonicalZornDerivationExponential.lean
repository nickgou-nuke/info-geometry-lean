import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
import InfoGeometry.Lie.CanonicalZornDerivationCentralKernel
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Canonical.ZornSpinor

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornDerivationExponential

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

local notation "CZ" => InfoGeometry.Lie.CanonicalZornDerivation.CZ

/-!
## Landing in the native real split-octonion automorphism group
-/

/--
The exponential flow of a canonical Zorn derivation, regarded as an element
of the repository-owned native real split-octonion automorphism group.
-/
noncomputable def zornFlowRealAut
    (D : canonicalZornDerivations)
    (t : ℝ) : RealSplitOctonionAut :=
  ⟨zornFlowLinearEquiv D.1 t, by
    constructor
    · apply InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.coordLE.injective
      rw [InfoGeometry.Lie.CanonicalZornDerivationExponential.coordLE_zornFlowLinearEquiv]
      have hcoord : coordEnd D.1
          (InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.coordLE (1 : CZ)) = 0 := by
        rw [coordEnd_apply_coordLE, derivation_apply_one]
        simp
      exact InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv_fixed_of_derivation_eq_zero
        (coordEnd D.1)
        (InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.coordLE (1 : CZ)) hcoord t
    · intro X Y
      exact zornFlow_map_mul D.1 D.2 t X Y⟩

/-- The underlying linear equivalence is exactly the exponential Zorn flow. -/
@[simp]
theorem zornFlowRealAut_coe
    (D : canonicalZornDerivations)
    (t : ℝ) :
    ((zornFlowRealAut D t : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) =
      zornFlowLinearEquiv D.1 t := by
  rfl

/-- Pointwise readback of the native automorphism into the exponential flow. -/
@[simp]
theorem zornFlowRealAut_apply
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    ((zornFlowRealAut D t : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) X =
      zornFlowLinearEquiv D.1 t X := by
  rfl

/-- Every derivation exponential fixes the Zorn multiplicative unit. -/
@[simp]
theorem zornFlow_fixes_one
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (1 : CZ) = 1 := by
  simpa using
    (RealSplitOctonionAut.preserves_one (zornFlowRealAut D t))

/-- Every derivation exponential preserves the full nonassociative Zorn product. -/
theorem zornFlow_preserves_mul
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowLinearEquiv D.1 t (X * Y) =
      zornFlowLinearEquiv D.1 t X *
        zornFlowLinearEquiv D.1 t Y := by
  exact zornFlow_map_mul D.1 D.2 t X Y

/--
The exponential of every canonical derivation lands in the exact native
real split-octonion automorphism subgroup.
-/
theorem canonical_derivation_exponential_lands_in_realAut
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t ∈
      splitOctonionAutSubgroup (R := ℝ) := by
  exact (zornFlowRealAut D t).property

/-!
## Invariant consequences
-/

/-- The finite derivation flow preserves the canonical Zorn determinant. -/
@[simp]
theorem zornFlow_preserves_detZ
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    InfoGeometry.Canonical.ZornMatrix.detZ (zornFlowLinearEquiv D.1 t X) =
      InfoGeometry.Canonical.ZornMatrix.detZ X := by
  simpa using
    (RealSplitOctonionAut.preserves_detZ (zornFlowRealAut D t) X)

/-- The finite derivation flow preserves the canonical split null cone. -/
@[simp]
theorem zornFlow_preserves_null
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (zornFlowLinearEquiv D.1 t X) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  simpa using
    (RealSplitOctonionAut.preserves_null (zornFlowRealAut D t) X)

/-!
## One-parameter group in the native real automorphism group
-/

/-- Time zero gives the identity native real split-octonion automorphism. -/
@[simp]
theorem zornFlowRealAut_zero
    (D : canonicalZornDerivations) :
    zornFlowRealAut D 0 = (1 : RealSplitOctonionAut) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change zornFlowLinearEquiv D.1 0 X = X
  exact zornFlowLinearEquiv_zero_apply D.1 X

/--
The native real automorphism flow satisfies the additive time-composition law.
-/
theorem zornFlowRealAut_add
    (D : canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowRealAut D (s + t) =
      zornFlowRealAut D s * zornFlowRealAut D t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change
    zornFlowLinearEquiv D.1 (s + t) X =
      zornFlowLinearEquiv D.1 s
        (zornFlowLinearEquiv D.1 t X)
  exact zornFlow_add_apply D s t X

/-- Negative time is the inverse in the native real automorphism group. -/
@[simp]
theorem zornFlowRealAut_neg
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAut D (-t) =
      (zornFlowRealAut D t)⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change
    zornFlowLinearEquiv D.1 (-t) X =
      (zornFlowLinearEquiv D.1 t).symm X
  apply (zornFlowLinearEquiv D.1 t).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [← zornFlowLinearEquiv_add_apply D.1 t (-t)]
  simp

/--
The canonical derivation exponential as a genuine one-parameter subgroup of
the repository-owned native real split-octonion automorphism group.
-/
noncomputable def zornFlowRealAutGroupHom
    (D : canonicalZornDerivations) :
    Multiplicative ℝ →* RealSplitOctonionAut where
  toFun τ := zornFlowRealAut D τ.toAdd
  map_one' := by
    simp [zornFlowRealAut_zero]
  map_mul' σ τ := by
    simp [zornFlowRealAut_add]

@[simp]
theorem zornFlowRealAutGroupHom_apply
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd t) =
      zornFlowRealAut D t := by
  rfl

/-- Zero time maps to the identity automorphism. -/
@[simp]
theorem zornFlowRealAutGroupHom_zero
    (D : canonicalZornDerivations) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd 0) = 1 := by
  exact map_one (zornFlowRealAutGroupHom D)

/-- Additive time becomes composition in the native automorphism group. -/
theorem zornFlowRealAutGroupHom_add
    (D : canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd (s + t)) =
      zornFlowRealAutGroupHom D (Multiplicative.ofAdd s) *
        zornFlowRealAutGroupHom D (Multiplicative.ofAdd t) := by
  simp [map_mul]

/-- Negative time becomes the group inverse. -/
@[simp]
theorem zornFlowRealAutGroupHom_neg
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd (-t)) =
      (zornFlowRealAutGroupHom D (Multiplicative.ofAdd t))⁻¹ := by
  simp [map_inv]

/-!
## Time-one exponential and complete packet
-/

/-- The time-one derivation exponential in the native real automorphism group. -/
noncomputable def zornDerivationExpRealAut
    (D : canonicalZornDerivations) :
    RealSplitOctonionAut :=
  zornFlowRealAut D 1

@[simp]
theorem zornDerivationExpRealAut_apply
    (D : canonicalZornDerivations)
    (X : CZ) :
    ((zornDerivationExpRealAut D : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) X =
      zornDerivationExpAutomorphism D X := by
  rfl

/-- The time-one exponential preserves the Zorn determinant. -/
@[simp]
theorem zornDerivationExpRealAut_preserves_detZ
    (D : canonicalZornDerivations)
    (X : CZ) :
    InfoGeometry.Canonical.ZornMatrix.detZ (zornDerivationExpAutomorphism D X) =
      InfoGeometry.Canonical.ZornMatrix.detZ X := by
  simpa [zornDerivationExpRealAut_apply] using
    zornFlow_preserves_detZ D 1 X

/-- The time-one exponential preserves the canonical split null cone. -/
@[simp]
theorem zornDerivationExpRealAut_preserves_null
    (D : canonicalZornDerivations)
    (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (zornDerivationExpAutomorphism D X) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  simpa [zornDerivationExpRealAut_apply] using
    zornFlow_preserves_null D 1 X

end InfoGeometry.Canonical.CanonicalZornDerivationExponential
