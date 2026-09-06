import InfoGeometry.Lie.CanonicalZornDerivationExponential
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

/-!
# One-parameter automorphism group of a canonical Zorn derivation

For a canonical real Zorn derivation `D`, the exponential owner already
constructs

`zornFlowMulEquiv D t : MulAut CZ`.

This module proves the complete group law and packages the flow as a genuine
Mathlib monoid homomorphism

`Multiplicative ℝ →* MulAut CZ`.

The multiplicative type tag on `ℝ` is only a change of notation: multiplication
in `Multiplicative ℝ` is addition of real parameters.  Thus this is precisely
the one-parameter subgroup

`(ℝ, +) → Aut_mul(𝕆_s)`.

No global identification of `Aut(𝕆_s)` with split `G₂` is assumed.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

namespace CDE := InfoGeometry.Lie.ContinuousDerivationExponential
namespace CZDE := InfoGeometry.Lie.CanonicalZornDerivationExponential
namespace CZD := InfoGeometry.Lie.CanonicalZornDerivation

open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal

abbrev CZ := CZD.CZ
abbrev V8 := Fin 8 → ℝ

/-!
## Pointwise flow laws
-/

/--
The finite Zorn automorphism flow satisfies the additive parameter law
pointwise:

`Φ_(s+t)(X) = Φ_s(Φ_t(X))`.
-/
theorem zornFlow_add_apply
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ)
    (X : CZ) :
    CZDE.zornFlowMulEquiv D (s + t) X =
      CZDE.zornFlowMulEquiv D s
        (CZDE.zornFlowMulEquiv D t X) := by
  change
    CZDE.zornFlowLinearEquiv D.1 (s + t) X =
      CZDE.zornFlowLinearEquiv D.1 s
        (CZDE.zornFlowLinearEquiv D.1 t X)
  apply coordLE.injective
  rw [CZDE.coordLE_zornFlowLinearEquiv]
  rw [CZDE.coordLE_zornFlowLinearEquiv]
  rw [CZDE.coordLE_zornFlowLinearEquiv]
  have h := congrArg
    (fun T : V8 →L[ℝ] V8 => T (coordLE X))
    (CDE.flow_add (CZDE.coordEnd D.1) s t)
  simpa [mul_apply_eq_comp] using h

/-- Time zero acts identically pointwise. -/
@[simp]
theorem zornFlow_zero_apply
    (D : CZD.canonicalZornDerivations)
    (X : CZ) :
    CZDE.zornFlowMulEquiv D 0 X = X := by
  change CZDE.zornFlowLinearEquiv D.1 0 X = X
  exact CZDE.zornFlowLinearEquiv_zero_apply D.1 X

/-- Negative time is a left inverse of positive time. -/
@[simp]
theorem zornFlow_neg_apply_flow
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    CZDE.zornFlowMulEquiv D (-t)
        (CZDE.zornFlowMulEquiv D t X) = X := by
  rw [← zornFlow_add_apply D (-t) t X]
  simp

/-- Positive time is a left inverse of negative time. -/
@[simp]
theorem zornFlow_apply_neg_flow
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    CZDE.zornFlowMulEquiv D t
        (CZDE.zornFlowMulEquiv D (-t) X) = X := by
  rw [← zornFlow_add_apply D t (-t) X]
  simp

/-!
## Equality of automorphisms
-/

/-- The time-zero automorphism is the identity element of `MulAut CZ`. -/
@[simp]
theorem zornFlow_zero
    (D : CZD.canonicalZornDerivations) :
    CZDE.zornFlowMulEquiv D 0 = (1 : MulAut CZ) := by
  apply MulEquiv.ext
  intro X
  exact zornFlow_zero_apply D X

/-- The finite flow satisfies the group law as an equality in `MulAut CZ`. -/
theorem zornFlow_add
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ) :
    CZDE.zornFlowMulEquiv D (s + t) =
      CZDE.zornFlowMulEquiv D s * CZDE.zornFlowMulEquiv D t := by
  apply MulEquiv.ext
  intro X
  rw [MulAut.mul_apply]
  exact zornFlow_add_apply D s t X

/-- Negative time is the group inverse automorphism. -/
theorem zornFlow_neg
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    CZDE.zornFlowMulEquiv D (-t) =
      (CZDE.zornFlowMulEquiv D t)⁻¹ := by
  apply MulEquiv.ext
  intro X
  apply (CZDE.zornFlowMulEquiv D t).injective
  rw [MulAut.apply_inv_self]
  exact zornFlow_apply_neg_flow D t X

/-!
## Genuine one-parameter subgroup
-/

/--
The exponential flow of a canonical Zorn derivation as a genuine one-parameter
subgroup of the multiplicative automorphism group.

`Multiplicative ℝ` is the multiplicative type tag for the additive real group,
so its multiplication is real addition.
-/
noncomputable def zornFlowGroupHom
    (D : CZD.canonicalZornDerivations) :
    Multiplicative ℝ →* MulAut CZ where
  toFun τ := CZDE.zornFlowMulEquiv D τ.toAdd
  map_one' := by
    simpa using zornFlow_zero D
  map_mul' σ τ := by
    simpa using zornFlow_add D σ.toAdd τ.toAdd

@[simp]
theorem zornFlowGroupHom_apply
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    zornFlowGroupHom D (Multiplicative.ofAdd t) =
      CZDE.zornFlowMulEquiv D t := by
  rfl

@[simp]
theorem zornFlowGroupHom_zero
    (D : CZD.canonicalZornDerivations) :
    zornFlowGroupHom D (Multiplicative.ofAdd 0) = 1 := by
  exact map_one (zornFlowGroupHom D)

/-- Additive real parameters map to composition of automorphisms. -/
theorem zornFlowGroupHom_add
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowGroupHom D (Multiplicative.ofAdd (s + t)) =
      zornFlowGroupHom D (Multiplicative.ofAdd s) *
        zornFlowGroupHom D (Multiplicative.ofAdd t) := by
  simpa using map_mul (zornFlowGroupHom D)
    (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- Negative real time maps to the inverse automorphism. -/
theorem zornFlowGroupHom_neg
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    zornFlowGroupHom D (Multiplicative.ofAdd (-t)) =
      (zornFlowGroupHom D (Multiplicative.ofAdd t))⁻¹ := by
  simpa using map_inv (zornFlowGroupHom D) (Multiplicative.ofAdd t)

/-- The time-one element is exactly the previously defined exponential automorphism. -/
@[simp]
theorem zornFlowGroupHom_one_time
    (D : CZD.canonicalZornDerivations) :
    zornFlowGroupHom D (Multiplicative.ofAdd (1 : ℝ)) =
      CZDE.zornDerivationExpAutomorphism D := by
  rfl

/--
Complete one-parameter subgroup packet: identity, composition law, and inverse
law, all on the native `MulAut` carrier.
-/
theorem zorn_oneParameterGroup_packet
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowGroupHom D (Multiplicative.ofAdd 0) = 1 ∧
      zornFlowGroupHom D (Multiplicative.ofAdd (s + t)) =
        zornFlowGroupHom D (Multiplicative.ofAdd s) *
          zornFlowGroupHom D (Multiplicative.ofAdd t) ∧
      zornFlowGroupHom D (Multiplicative.ofAdd (-t)) =
        (zornFlowGroupHom D (Multiplicative.ofAdd t))⁻¹ := by
  exact ⟨zornFlowGroupHom_zero D,
    zornFlowGroupHom_add D s t,
    zornFlowGroupHom_neg D t⟩

end InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

end noncomputable section
