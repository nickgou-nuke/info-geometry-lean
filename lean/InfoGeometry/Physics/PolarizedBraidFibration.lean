import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Polarized Braid Fibration: two-sheet action over split-octonion phase space

This module formalizes the two-sheet braid transport over the split-octonion
chiral phase space `W = V⁺ ⊕ V⁻`.

## Mathematical corrections over earlier drafts

* There is only **one** braid group `B₃`, not two independent monoids.
  The positive monoid `B₃⁺` embeds in `B₃`; the negative cone is the opposite
  monoid `(B₃⁺)ᵒᵖ ≅ B₃⁻` obtained by inverting Artin generators.
* The polarized transport is parameterized by a one-sheet permutation
  representation `B₃ →* Equiv.Perm Vec`; this file does not claim that the
  inverse-readback is itself a second monoid action.
* The lower-sheet action is the readback `ρ(g⁻¹)` on the second factor,
  not a second independent monoid action.
* `sheetSwap : W ≃ W` is the involution exchanging the two sheets; it
  intertwines `ρ(g)` and `ρ(g⁻¹)`.
* The split-octonion upper/lower pairing is a concrete bilinear pairing
  `U(q) * L(p)`, not an Ore localization.
* The Zorn carrier has two 3-vector components `v, w : Fin 3 → ℝ`,
  giving three positive chiral planes `(s₁⁺, s₂⁺, s₃⁺)` and three negative
  chiral planes `(s₁⁻, s₂⁻, s₃⁻)`.
* The cross-product identities are retained as Zorn algebra identities only;
  no braid, framed-braid, or triality interpretation is asserted.

## Kernel-checked theorems

* `mixed_sheet_contraction`: `(U_i * L_j).a = δᵢⱼ`
* `sheetSwap_involution`: `sheetSwap` is an involution
* `sheetSwap_intertwining`: `sheetSwap` conjugates `ρ(g)` to `ρ(g⁻¹)`
-/

namespace InfoGeometry.Physics.PolarizedBraidFibration

open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-! ## Phase space carrier -/

/-- The phase space `W = V⁺ × V⁻` pairs upper and lower chiral vectors. -/
abbrev Phase := Vec × Vec
abbrev ChiralPerm := Equiv.Perm Vec

/-! ## Split-octonion chiral basis -/

/-- Upper chiral basis element `U(q)` embedded into the real Zorn carrier. -/
def upperZornBasis (q : Vec) : ZornCoord :=
  upperVectorZorn q

/-- Lower chiral basis element `L(p)` embedded into the real Zorn carrier. -/
def lowerZornBasis (p : Vec) : ZornCoord :=
  lowerVectorZorn p

/-! ## Concrete bilinear pairing (not Ore localization) -/

/-- The scalar `a`-component of the upper/lower Zorn product.
    This is the genuine split-octonion mixed-sheet contraction:
    `(U(q) * L(p)).a = q · p`. -/
def mixedSheetScalar (q p : Vec) : ℝ :=
  dot3 q p

/-- The mixed-sheet contraction is symmetric. -/
theorem mixedSheetScalar_comm (q p : Vec) :
    mixedSheetScalar q p = mixedSheetScalar p q := by
  exact dot3_comm q p

/-- The mixed-sheet contraction is bilinear in the first argument. -/
theorem mixedSheetScalar_add_left (q r p : Vec) :
    mixedSheetScalar (q + r) p = mixedSheetScalar q p + mixedSheetScalar r p := by
  simp [mixedSheetScalar, dot3]
  ring

theorem mixedSheetScalar_smul_left (a : ℝ) (q p : Vec) :
    mixedSheetScalar (a • q) p = a * mixedSheetScalar q p := by
  simp [mixedSheetScalar, dot3]
  ring

/-- Kronecker-delta contraction on basis elements: `(U_i * L_j).a = δᵢⱼ`. -/
theorem mixed_sheet_contraction (i j : Fin 3) :
    (zornMul (upperVectorZorn (Vec3.basis i)) (lowerVectorZorn (Vec3.basis j))).1 =
      if i = j then (1 : ℝ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [zornMul, upperVectorZorn, lowerVectorZorn, dot3, Vec3.basis,
      zornMk, cross3]

/-! ## Sheet swap involution -/

/-- The sheet swap involution exchanges the upper and lower chiral vectors.
    It is only a carrier-level involution; no Garside or physical symmetry is
    identified here. -/
def sheetSwap (z : Phase) : Phase :=
  (z.2, z.1)

/-- `sheetSwap` is an involution. -/
@[simp] theorem sheetSwap_involution (z : Phase) :
    sheetSwap (sheetSwap z) = z := by
  simp [sheetSwap]

/-! ## Polarized braid action -/

/-- The polarized braid action on the phase space `W = V⁺ × V⁻`.
    For a group element `g : B₃`, the upper sheet transforms by `ρ(g)`
    and the lower sheet transforms by `ρ(g⁻¹)`. -/
def polarizedBraidAction (act : B3 →* ChiralPerm) (g : B3) (z : Phase) : Phase :=
  (act g z.1, act g⁻¹ z.2)

/-- The polarized action respects the sheet swap involution:
    `J_sheet ∘ ρ(g) = ρ(g⁻¹) ∘ J_sheet`. -/
theorem sheetSwap_intertwining (act : B3 →* ChiralPerm) (g : B3) (z : Phase) :
    sheetSwap (polarizedBraidAction act g z) =
      polarizedBraidAction act g⁻¹ (sheetSwap z) := by
  simp [sheetSwap, polarizedBraidAction]

end InfoGeometry.Physics.PolarizedBraidFibration
