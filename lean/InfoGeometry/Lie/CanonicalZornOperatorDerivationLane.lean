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
    (operatorAdjointDerivation D : Module.End ℝ EndCZ) T =
      D.1 * T - T * D.1 := by
  change ((operatorAdjointDerivation D : OperatorDer) : Module.End ℝ EndCZ) T = _
  rfl

/-- The adjoint action is a native Lie homomorphism into operator-algebra
derivations. -/
theorem operatorAdjointDerivation_map_lie
    (D E : ZornDer) :
    operatorAdjointDerivation ⁅D, E⁆ =
      ⁅operatorAdjointDerivation D, operatorAdjointDerivation E⁆ := by
  apply Subtype.ext
  simpa [operatorAdjointDerivation] using
    (LieAlgebra.ad ℝ EndCZ).map_lie (D : EndCZ) (E : EndCZ)

noncomputable def operatorAdjointAction : ZornDer →ₗ⁅ℝ⁆ OperatorDer where
  toFun := operatorAdjointDerivation
  map_add' := by
    intro D E
    apply Subtype.ext
    simpa [operatorAdjointDerivation] using
      (map_add (LieAlgebra.ad ℝ EndCZ) D.1 E.1)
  map_smul' := by
    intro r D
    apply Subtype.ext
    simpa [operatorAdjointDerivation] using
      (map_smul (LieAlgebra.ad ℝ EndCZ) r D.1)
  map_lie' := operatorAdjointDerivation_map_lie _ _

@[simp] theorem operatorAdjointAction_apply
    (D : ZornDer) (T : EndCZ) :
    (operatorAdjointAction D : Module.End ℝ EndCZ) T =
      D.1 * T - T * D.1 := by
  simpa [operatorAdjointAction, operatorAdjointDerivation]
    using operatorAdjointDerivation_apply D T

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
  have hOnLeft' :
      D.1 * InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x -
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x * D.1 =
        E.1 * InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x -
          InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x * E.1 := by
    simpa only [operatorAdjointAction_apply] using hOnLeft
  have hBracket :
      ⁅D.1, InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x⁆ =
        ⁅E.1, InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x⁆ := by
    simpa [LieRing.of_associative_ring_bracket] using hOnLeft'
  rw [derivation_commutator_leftRegular D.1 D.2 x,
    derivation_commutator_leftRegular E.1 E.2 x] at hBracket
  have hAtOne := LinearMap.congr_fun hBracket (1 : CZ)
  change D.1 x * (1 : CZ) = E.1 x * (1 : CZ) at hAtOne
  have hAtOne' := hAtOne
  simp [InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross] at hAtOne'
  rcases hAtOne' with ⟨ha, hb, hx, hy⟩
  rcases hx with ⟨hx0, hx1, hx2⟩
  rcases hy with ⟨hy0, hy1, hy2⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · exact ha
  · exact hb
  · funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
  · funext i
    fin_cases i
    · exact hy0
    · exact hy1
    · exact hy2

/-- Canonical split-octonion derivations as a faithful derivation lane on the
associative operator algebra `End(CZ)`. -/
noncomputable def canonicalZornOperatorDerivationLane :
    DerivationLieLane ℝ EndCZ where
  L := ZornDer
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := operatorAdjointAction
  faithful := operatorAdjointAction_injective

/-! The action-only projection is the canonical interface for constructions
which require a Lie action on a module, but do not require the faithfulness
field carried by `DerivationLieLane`. -/
noncomputable def canonicalZornOperatorActionLane :
    LieActionLane ℝ EndCZ where
  L := ZornDer
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act :=
    { toFun := fun D => (operatorAdjointAction D : Module.End ℝ EndCZ)
      map_add' := by
        intro D E
        apply LinearMap.ext
        intro T
        change (D.1 + E.1) * T - T * (D.1 + E.1) =
          (D.1 * T - T * D.1) + (E.1 * T - T * E.1)
        noncomm_ring
      map_smul' := by
        intro r D
        apply LinearMap.ext
        intro T
        change (r • D.1) * T - T * (r • D.1) =
          r • (D.1 * T - T * D.1)
        simp only [smul_sub, smul_mul_assoc, mul_smul_comm]
      map_lie' := by
        intro D E
        simpa using congrArg (fun δ : OperatorDer =>
          (δ : Module.End ℝ EndCZ))
          (operatorAdjointDerivation_map_lie D E) }

@[simp] theorem canonicalZornOperatorDerivationLane_act
    (D : ZornDer) (T : EndCZ) :
    (canonicalZornOperatorDerivationLane.act D : Module.End ℝ EndCZ) T =
      D.1 * T - T * D.1 := by
  change (operatorAdjointAction D : Module.End ℝ EndCZ) T = _
  exact operatorAdjointAction_apply D T

@[simp] theorem canonicalZornOperatorDerivationLane_operatorAction
    (D : ZornDer) (T : EndCZ) :
    canonicalZornOperatorDerivationLane.operatorAction D T =
      D.1 * T - T * D.1 := by
  change (operatorAdjointAction D : Module.End ℝ EndCZ) T = _
  exact operatorAdjointAction_apply D T

end InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
