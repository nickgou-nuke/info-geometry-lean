import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.Algebra.DerivationLieLaneRepresentation
import InfoGeometry.Lie.CanonicalZornDerivationLane
import InfoGeometry.Lie.SplitOctonionRegularActionIntertwiner

/-!
# Canonical Zorn derivations acting on the associative operator algebra

The canonical split-octonion derivations act on the nonassociative Zorn
carrier.  Their operator lift acts on `End(CZ)` by the associative commutator

`T ↦ [D,T] = D*T - T*D`.

This file packages that adjoint action as a faithful `DerivationLieLane` on
the associative endomorphism algebra.  Faithfulness is not postulated and no
classification of the center of `End(CZ)` is used: if the commutator action of
`D` is zero, then `[D,L_x] = L_(D x)` is zero for every `x`; evaluation at the
Zorn unit gives `D x = 0`.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornOperatorDerivationLane

open InfoGeometry.Algebra
open InfoGeometry.Algebra.NonAssocDerivation
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionRegularActionIntertwiner
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev ZornDer := canonicalZornDerivations
abbrev OperatorDer := derivations ℝ EndCZ

/-- The inner commutator with a canonical Zorn derivation, regarded as a
Leibniz derivation of the associative operator algebra. -/
noncomputable def operatorAdjointDerivation (D : ZornDer) : OperatorDer :=
  ⟨LieAlgebra.ad ℝ EndCZ D.1, by
    intro S T
    change
      D.1 * (S * T) - (S * T) * D.1 =
        (D.1 * S - S * D.1) * T +
          S * (D.1 * T - T * D.1)
    noncomm_ring⟩

@[simp] theorem operatorAdjointDerivation_apply
    (D : ZornDer) (T : EndCZ) :
    operatorAdjointDerivation D T = D.1 * T - T * D.1 :=
  rfl

/-- The adjoint action is a native Lie homomorphism into operator-algebra
derivations. -/
noncomputable def operatorAdjointAction : ZornDer →ₗ⁅ℝ⁆ OperatorDer where
  toFun := operatorAdjointDerivation
  map_add' D E := by
    apply Subtype.ext
    exact (LieAlgebra.ad ℝ EndCZ).map_add D.1 E.1
  map_smul' r D := by
    apply Subtype.ext
    exact (LieAlgebra.ad ℝ EndCZ).map_smul r D.1
  map_lie' D E := by
    apply Subtype.ext
    exact (LieAlgebra.ad ℝ EndCZ).map_lie D.1 E.1

@[simp] theorem operatorAdjointAction_apply
    (D : ZornDer) (T : EndCZ) :
    operatorAdjointAction D T = D.1 * T - T * D.1 :=
  rfl

/-- The adjoint operator action is faithful on canonical Zorn derivations.
The proof detects a derivation through its commutator with every left-regular
multiplication operator. -/
theorem operatorAdjointAction_injective :
    Function.Injective operatorAdjointAction := by
  intro D E hDE
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hOnLeft := congrArg
    (fun δ : OperatorDer =>
      (δ : Module.End ℝ EndCZ)
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x))
    hDE
  change
    ⁅D.1,
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x⁆ =
      ⁅E.1,
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x⁆
    at hOnLeft
  rw [derivation_commutator_leftRegular D.1 D.2 x,
    derivation_commutator_leftRegular E.1 E.2 x] at hOnLeft
  have hAtOne := LinearMap.congr_fun hOnLeft (1 : CZ)
  change D.1 x * (1 : CZ) = E.1 x * (1 : CZ) at hAtOne
  simpa only [zMul_one] using hAtOne

/-- Canonical split-octonion derivations as a faithful derivation lane on the
associative operator algebra `End(CZ)`. -/
noncomputable def canonicalZornOperatorDerivationLane :
    DerivationLieLane ℝ EndCZ where
  L := ZornDer
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := operatorAdjointAction
  faithful := operatorAdjointAction_injective

@[simp] theorem canonicalZornOperatorDerivationLane_act
    (D : ZornDer) (T : EndCZ) :
    canonicalZornOperatorDerivationLane.act D T =
      D.1 * T - T * D.1 :=
  rfl

@[simp] theorem canonicalZornOperatorDerivationLane_operatorAction
    (D : ZornDer) (T : EndCZ) :
    canonicalZornOperatorDerivationLane.operatorAction D T =
      D.1 * T - T * D.1 :=
  rfl

end InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
