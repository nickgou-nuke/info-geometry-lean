import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Canonical.SplitOctonionAutomorphism

/-!
# Canonical Zorn derivation exponential into the native real automorphism group

This module closes the exact finite-automorphism landing theorem for canonical
real split-octonion derivations.

The analytic owner
`InfoGeometry.Lie.CanonicalZornDerivationExponential` proves that a canonical
Zorn derivation `D` exponentiates to a multiplicative linear equivalence

`zornFlowLinearEquiv D t : ZornMatrix ℝ ≃ₗ[ℝ] ZornMatrix ℝ`.

The automorphism owner
`InfoGeometry.Canonical.SplitOctonionAutomorphism` defines
`RealSplitOctonionAut` as the subgroup of real linear equivalences preserving
both the Zorn unit and the Zorn product.

This file proves that every exponential derivation flow lies in that native
automorphism group and packages the complete one-parameter flow as

`Multiplicative ℝ →* RealSplitOctonionAut`.

Since multiplication in `Multiplicative ℝ` is addition of real parameters,
this is the precise theorem-safe form of

`(ℝ,+) → Aut(𝕆_s)`.

As consequences, the exponential flow preserves the canonical Zorn
determinant/composition norm and the split null cone, using the already-proved
native automorphism theorems.

No global identification

`RealSplitOctonionAut ≃ G₂(2)`

is asserted here. That remains a distinct global classification theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornDerivationExponential

namespace CZD := InfoGeometry.Lie.CanonicalZornDerivation
namespace CZDE := InfoGeometry.Lie.CanonicalZornDerivationExponential
namespace CZDG := InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

open InfoGeometry.Canonical

abbrev CZ := CZD.CZ

/-!
## Landing in the native real split-octonion automorphism group
-/

/--
The exponential flow of a canonical Zorn derivation, regarded as an element
of the repository-owned native real split-octonion automorphism group.
-/
noncomputable def zornFlowRealAut
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) : RealSplitOctonionAut :=
  ⟨CZDE.zornFlowLinearEquiv D.1 t, by
    constructor
    · change CZDE.zornFlowLinearEquiv D.1 t (1 : CZ) = 1
      exact CZDE.zornFlow_map_one D.1 D.2 t
    · intro X Y
      exact CZDE.zornFlow_map_mul D.1 D.2 t X Y⟩

/-- The underlying linear equivalence is exactly the exponential Zorn flow. -/
@[simp]
theorem zornFlowRealAut_coe
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    ((zornFlowRealAut D t : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) =
      CZDE.zornFlowLinearEquiv D.1 t := by
  rfl

/-- Pointwise readback of the native automorphism into the exponential flow. -/
@[simp]
theorem zornFlowRealAut_apply
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    ((zornFlowRealAut D t : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) X =
      CZDE.zornFlowLinearEquiv D.1 t X := by
  rfl

/-- Every derivation exponential fixes the Zorn multiplicative unit. -/
@[simp]
theorem zornFlow_fixes_one
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    CZDE.zornFlowLinearEquiv D.1 t (1 : CZ) = 1 := by
  simpa using
    (RealSplitOctonionAut.preserves_one (zornFlowRealAut D t))

/-- Every derivation exponential preserves the full nonassociative Zorn product. -/
theorem zornFlow_preserves_mul
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X Y : CZ) :
    CZDE.zornFlowLinearEquiv D.1 t (X * Y) =
      CZDE.zornFlowLinearEquiv D.1 t X *
        CZDE.zornFlowLinearEquiv D.1 t Y := by
  exact CZDE.zornFlow_map_mul D.1 D.2 t X Y

/--
The exponential of every canonical derivation lands in the exact native
real split-octonion automorphism subgroup.
-/
theorem canonical_derivation_exponential_lands_in_realAut
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    CZDE.zornFlowLinearEquiv D.1 t ∈
      splitOctonionAutSubgroup (R := ℝ) := by
  exact (zornFlowRealAut D t).property

/-!
## Invariant consequences
-/

/-- The finite derivation flow preserves the canonical Zorn determinant. -/
@[simp]
theorem zornFlow_preserves_detZ
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    ZornMatrix.detZ (CZDE.zornFlowLinearEquiv D.1 t X) =
      ZornMatrix.detZ X := by
  simpa using
    (RealSplitOctonionAut.preserves_detZ (zornFlowRealAut D t) X)

/-- The finite derivation flow preserves the canonical split null cone. -/
@[simp]
theorem zornFlow_preserves_null
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (CZDE.zornFlowLinearEquiv D.1 t X) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        X := by
  simpa using
    (RealSplitOctonionAut.preserves_null (zornFlowRealAut D t) X)

/-!
## One-parameter group in the native real automorphism group
-/

/-- Time zero gives the identity native real split-octonion automorphism. -/
@[simp]
theorem zornFlowRealAut_zero
    (D : CZD.canonicalZornDerivations) :
    zornFlowRealAut D 0 = (1 : RealSplitOctonionAut) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change CZDE.zornFlowLinearEquiv D.1 0 X = X
  exact CZDE.zornFlowLinearEquiv_zero_apply D.1 X

/--
The native real automorphism flow satisfies the additive time-composition law.
-/
theorem zornFlowRealAut_add
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowRealAut D (s + t) =
      zornFlowRealAut D s * zornFlowRealAut D t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change
    CZDE.zornFlowLinearEquiv D.1 (s + t) X =
      CZDE.zornFlowLinearEquiv D.1 s
        (CZDE.zornFlowLinearEquiv D.1 t X)
  exact CZDG.zornFlow_add_apply D s t X

/-- Negative time is the inverse in the native real automorphism group. -/
@[simp]
theorem zornFlowRealAut_neg
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAut D (-t) =
      (zornFlowRealAut D t)⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change
    CZDE.zornFlowLinearEquiv D.1 (-t) X =
      (CZDE.zornFlowLinearEquiv D.1 t).symm X
  apply (CZDE.zornFlowLinearEquiv D.1 t).injective
  change
    CZDE.zornFlowLinearEquiv D.1 t
        (CZDE.zornFlowLinearEquiv D.1 (-t) X) = X
  change
    CZDE.zornFlowMulEquiv D t
        (CZDE.zornFlowMulEquiv D (-t) X) = X
  exact CZDG.zornFlow_apply_neg_flow D t X

/--
The canonical derivation exponential as a genuine one-parameter subgroup of
the repository-owned native real split-octonion automorphism group.
-/
noncomputable def zornFlowRealAutGroupHom
    (D : CZD.canonicalZornDerivations) :
    Multiplicative ℝ →* RealSplitOctonionAut where
  toFun τ := zornFlowRealAut D τ.toAdd
  map_one' := by
    simpa using zornFlowRealAut_zero D
  map_mul' σ τ := by
    simpa using zornFlowRealAut_add D σ.toAdd τ.toAdd

@[simp]
theorem zornFlowRealAutGroupHom_apply
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd t) =
      zornFlowRealAut D t := by
  rfl

/-- Zero time maps to the identity automorphism. -/
@[simp]
theorem zornFlowRealAutGroupHom_zero
    (D : CZD.canonicalZornDerivations) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd 0) = 1 := by
  exact map_one (zornFlowRealAutGroupHom D)

/-- Additive time becomes composition in the native automorphism group. -/
theorem zornFlowRealAutGroupHom_add
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd (s + t)) =
      zornFlowRealAutGroupHom D (Multiplicative.ofAdd s) *
        zornFlowRealAutGroupHom D (Multiplicative.ofAdd t) := by
  simpa using
    map_mul (zornFlowRealAutGroupHom D)
      (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- Negative time becomes the group inverse. -/
@[simp]
theorem zornFlowRealAutGroupHom_neg
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd (-t)) =
      (zornFlowRealAutGroupHom D (Multiplicative.ofAdd t))⁻¹ := by
  simpa using
    map_inv (zornFlowRealAutGroupHom D) (Multiplicative.ofAdd t)

/-!
## Time-one exponential and complete packet
-/

/-- The time-one derivation exponential in the native real automorphism group. -/
noncomputable def zornDerivationExpRealAut
    (D : CZD.canonicalZornDerivations) :
    RealSplitOctonionAut :=
  zornFlowRealAut D 1

@[simp]
theorem zornDerivationExpRealAut_apply
    (D : CZD.canonicalZornDerivations)
    (X : CZ) :
    ((zornDerivationExpRealAut D : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) X =
      CZDE.zornDerivationExpAutomorphism D X := by
  rfl

/-- The time-one exponential preserves the Zorn determinant. -/
@[simp]
theorem zornDerivationExpRealAut_preserves_detZ
    (D : CZD.canonicalZornDerivations)
    (X : CZ) :
    ZornMatrix.detZ (CZDE.zornDerivationExpAutomorphism D X) =
      ZornMatrix.detZ X := by
  simpa [zornDerivationExpRealAut_apply] using
    zornFlow_preserves_detZ D 1 X

/-- Complete theorem-safe finite automorphism packet for a canonical derivation. -/
theorem canonical_derivation_realAut_packet
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ)
    (X Y : CZ) :
    CZDE.zornFlowLinearEquiv D.1 t (1 : CZ) = 1 ∧
      CZDE.zornFlowLinearEquiv D.1 t (X * Y) =
        CZDE.zornFlowLinearEquiv D.1 t X *
          CZDE.zornFlowLinearEquiv D.1 t Y ∧
      ZornMatrix.detZ (CZDE.zornFlowLinearEquiv D.1 t X) =
        ZornMatrix.detZ X ∧
      zornFlowRealAut D (s + t) =
        zornFlowRealAut D s * zornFlowRealAut D t ∧
      zornFlowRealAut D (-t) =
        (zornFlowRealAut D t)⁻¹ := by
  exact ⟨
    zornFlow_fixes_one D t,
    zornFlow_preserves_mul D t X Y,
    zornFlow_preserves_detZ D t X,
    zornFlowRealAut_add D s t,
    zornFlowRealAut_neg D t⟩

end InfoGeometry.Canonical.CanonicalZornDerivationExponential

end noncomputable section