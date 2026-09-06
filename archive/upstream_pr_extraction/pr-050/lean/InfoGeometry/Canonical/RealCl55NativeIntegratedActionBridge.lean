import Mathlib
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
import InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

/-!
# Native transport of a supplied finite group action

This owner transports the already supplied `G2IntegratedAction` from the
finite matrix carrier to the native continuous-linear-map carrier.  It is a
consumer bridge: it does not construct an integration of a Lie algebra, nor
does it assert a standard equivariant KKO/Kasparov class.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge

open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge

abbrev NativeSpinorCLM := RealCl55FiniteModuleEndBridge.NativeSpinorCLM
abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

variable {G : Type*} [Group G]

/-- Native continuous-linear-map action obtained from a supplied matrix action. -/
noncomputable def nativeIntegratedAction
    (act : G2IntegratedAction G) : G →* NativeSpinorCLM where
  toFun g := nativeContinuous (act.U g : Mat32)
  map_one' := by
    change nativeContinuous ((act.U 1 : Mat32GL) : Mat32) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier
    rw [map_one]
    exact nativeContinuous_one
  map_mul' g h := by
    change nativeContinuous ((act.U (g * h) : Mat32GL) : Mat32) =
      (nativeContinuous ((act.U g : Mat32GL) : Mat32)).comp
        (nativeContinuous ((act.U h : Mat32GL) : Mat32))
    rw [map_mul, Units.val_mul, nativeContinuous_mul]

@[simp] theorem nativeIntegratedAction_apply
    (act : G2IntegratedAction G) (g : G) :
    nativeIntegratedAction act g = nativeContinuous (act.U g : Mat32) := rfl

/-- A supplied action together with its native covariance laws. -/
structure NativeIntegratedActionDatum (act : G2IntegratedAction G) where
  action : G →* NativeSpinorCLM
  action_eq : action = nativeIntegratedAction act
  commutes_hodge (g : G) :
    (action g).comp nativeHodgeDirac =
      nativeHodgeDirac.comp (action g)
  commutes_chirality (g : G) :
    (action g).comp nativeChirality =
      nativeChirality.comp (action g)
  commutes_normalized_dirac (g : G) :
    (action g).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (action g)

theorem nativeIntegratedAction_commutes_hodge
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeHodgeDirac =
      nativeHodgeDirac.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous embeddedSplitOctonionHodgeDirac) =
    (nativeContinuous embeddedSplitOctonionHodgeDirac).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous (act.commutes_hodge g)

theorem nativeIntegratedAction_commutes_chirality
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChirality =
      nativeChirality.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous MasterChirality) =
    (nativeContinuous MasterChirality).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous (act.commutes_chirality g)

theorem nativeIntegratedAction_commutes_normalized_dirac
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous ((1 / 2 : ℝ) • embeddedSplitOctonionHodgeDirac)) =
    (nativeContinuous ((1 / 2 : ℝ) • embeddedSplitOctonionHodgeDirac)).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  rw [mul_smul_comm, smul_mul_assoc, act.commutes_hodge g]

theorem nativeIntegratedAction_commutes_projectorPlus
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChiralProjectorPlus =
      nativeChiralProjectorPlus.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous masterChiralProjectorPlus) =
    (nativeContinuous masterChiralProjectorPlus).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous (g2_integrated_comm_projectorPlus act g)

theorem nativeIntegratedAction_commutes_projectorMinus
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChiralProjectorMinus =
      nativeChiralProjectorMinus.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous masterChiralProjectorMinus) =
    (nativeContinuous masterChiralProjectorMinus).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous (g2_integrated_comm_projectorMinus act g)

theorem nativeIntegratedAction_commutes_chiralDiracPlus
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChiralDiracPlus =
      nativeChiralDiracPlus.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous masterChiralDiracPlus) =
    (nativeContinuous masterChiralDiracPlus).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  apply congrArg nativeContinuous
  rw [masterChiralDiracPlus_eq_projectorMinus_mul_hodge]
  calc
    (act.U g : Mat32) *
        (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) =
        ((act.U g : Mat32) * masterChiralProjectorMinus) *
          embeddedSplitOctonionHodgeDirac := by
            simp only [Matrix.mul_assoc]
    _ = (masterChiralProjectorMinus * (act.U g : Mat32)) *
          embeddedSplitOctonionHodgeDirac := by
            rw [g2_integrated_comm_projectorMinus act g]
    _ = masterChiralProjectorMinus *
          ((act.U g : Mat32) * embeddedSplitOctonionHodgeDirac) := by
            simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorMinus *
          (embeddedSplitOctonionHodgeDirac * (act.U g : Mat32)) := by
            rw [act.commutes_hodge g]
    _ = (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac) *
          (act.U g : Mat32) := by
            simp only [Matrix.mul_assoc]

theorem nativeIntegratedAction_commutes_chiralDiracMinus
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChiralDiracMinus =
      nativeChiralDiracMinus.comp (nativeIntegratedAction act g) := by
  rw [nativeIntegratedAction_apply]
  change (nativeContinuous (act.U g : Mat32)).comp
      (nativeContinuous masterChiralDiracMinus) =
    (nativeContinuous masterChiralDiracMinus).comp
      (nativeContinuous (act.U g : Mat32))
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  apply congrArg nativeContinuous
  rw [masterChiralDiracMinus_eq_projectorPlus_mul_hodge]
  calc
    (act.U g : Mat32) *
        (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) =
        ((act.U g : Mat32) * masterChiralProjectorPlus) *
          embeddedSplitOctonionHodgeDirac := by
            simp only [Matrix.mul_assoc]
    _ = (masterChiralProjectorPlus * (act.U g : Mat32)) *
          embeddedSplitOctonionHodgeDirac := by
            rw [g2_integrated_comm_projectorPlus act g]
    _ = masterChiralProjectorPlus *
          ((act.U g : Mat32) * embeddedSplitOctonionHodgeDirac) := by
            simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorPlus *
          (embeddedSplitOctonionHodgeDirac * (act.U g : Mat32)) := by
            rw [act.commutes_hodge g]
    _ = (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac) *
          (act.U g : Mat32) := by
            simp only [Matrix.mul_assoc]

theorem nativeIntegratedAction_commutes_hodgeLaplacian
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeHodgeLaplacian =
      nativeHodgeLaplacian.comp (nativeIntegratedAction act g) := by
  unfold nativeHodgeLaplacian
  calc
    (nativeIntegratedAction act g).comp
        (nativeHodgeDirac.comp nativeHodgeDirac) =
        ((nativeIntegratedAction act g).comp nativeHodgeDirac).comp
          nativeHodgeDirac := by rw [ContinuousLinearMap.comp_assoc]
    _ = (nativeHodgeDirac.comp (nativeIntegratedAction act g)).comp
          nativeHodgeDirac := by
          rw [nativeIntegratedAction_commutes_hodge act g]
    _ = nativeHodgeDirac.comp
          ((nativeIntegratedAction act g).comp nativeHodgeDirac) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = nativeHodgeDirac.comp
          (nativeHodgeDirac.comp (nativeIntegratedAction act g)) := by
          rw [nativeIntegratedAction_commutes_hodge act g]
    _ = (nativeHodgeDirac.comp nativeHodgeDirac).comp
          (nativeIntegratedAction act g) := by
          rw [ContinuousLinearMap.comp_assoc]

theorem nativeIntegratedAction_commutes_chiralLaplacianPlus
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChiralLaplacianPlus =
      nativeChiralLaplacianPlus.comp (nativeIntegratedAction act g) := by
  unfold nativeChiralLaplacianPlus
  calc
    (nativeIntegratedAction act g).comp
        (nativeChiralDiracMinus.comp nativeChiralDiracPlus) =
        ((nativeIntegratedAction act g).comp nativeChiralDiracMinus).comp
          nativeChiralDiracPlus := by rw [ContinuousLinearMap.comp_assoc]
    _ = (nativeChiralDiracMinus.comp (nativeIntegratedAction act g)).comp
          nativeChiralDiracPlus := by
          rw [nativeIntegratedAction_commutes_chiralDiracMinus act g]
    _ = nativeChiralDiracMinus.comp
          ((nativeIntegratedAction act g).comp nativeChiralDiracPlus) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = nativeChiralDiracMinus.comp
          (nativeChiralDiracPlus.comp (nativeIntegratedAction act g)) := by
          rw [nativeIntegratedAction_commutes_chiralDiracPlus act g]
    _ = (nativeChiralDiracMinus.comp nativeChiralDiracPlus).comp
          (nativeIntegratedAction act g) := by
          rw [ContinuousLinearMap.comp_assoc]

theorem nativeIntegratedAction_commutes_chiralLaplacianMinus
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp nativeChiralLaplacianMinus =
      nativeChiralLaplacianMinus.comp (nativeIntegratedAction act g) := by
  unfold nativeChiralLaplacianMinus
  calc
    (nativeIntegratedAction act g).comp
        (nativeChiralDiracPlus.comp nativeChiralDiracMinus) =
        ((nativeIntegratedAction act g).comp nativeChiralDiracPlus).comp
          nativeChiralDiracMinus := by rw [ContinuousLinearMap.comp_assoc]
    _ = (nativeChiralDiracPlus.comp (nativeIntegratedAction act g)).comp
          nativeChiralDiracMinus := by
          rw [nativeIntegratedAction_commutes_chiralDiracPlus act g]
    _ = nativeChiralDiracPlus.comp
          ((nativeIntegratedAction act g).comp nativeChiralDiracMinus) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = nativeChiralDiracPlus.comp
          (nativeChiralDiracMinus.comp (nativeIntegratedAction act g)) := by
          rw [nativeIntegratedAction_commutes_chiralDiracMinus act g]
    _ = (nativeChiralDiracPlus.comp nativeChiralDiracMinus).comp
          (nativeIntegratedAction act g) := by
          rw [ContinuousLinearMap.comp_assoc]

/-! A native finite equivariant package, still deliberately below standard
equivariant KKO theory. -/

structure NativeSuppliedEquivariantFiniteFredholmDatum
    (act : G2IntegratedAction G) where
  base : NativeFiniteFredholmDatum
  action : G →* NativeSpinorCLM
  action_eq : action = nativeIntegratedAction act
  action_commutes_chirality (g : G) :
    (action g).comp base.gamma = base.gamma.comp (action g)
  action_commutes_hodge (g : G) :
    (action g).comp nativeHodgeDirac =
      nativeHodgeDirac.comp (action g)
  action_commutes_F (g : G) :
    (action g).comp base.F = base.F.comp (action g)

def canonicalNativeSuppliedEquivariantFiniteFredholmDatum
    (act : G2IntegratedAction G) :
    NativeSuppliedEquivariantFiniteFredholmDatum act where
  base := canonicalNativeFiniteFredholmDatum
  action := nativeIntegratedAction act
  action_eq := rfl
  action_commutes_chirality := by
    intro g
    exact nativeIntegratedAction_commutes_chirality act g
  action_commutes_hodge := by
    intro g
    exact nativeIntegratedAction_commutes_hodge act g
  action_commutes_F := by
    intro g
    exact nativeIntegratedAction_commutes_normalized_dirac act g

theorem canonicalNativeSuppliedEquivariantFiniteFredholmDatum_F
    (act : G2IntegratedAction G) :
    (canonicalNativeSuppliedEquivariantFiniteFredholmDatum act).base.F =
      nativeNormalizedDirac := rfl

theorem canonicalNativeSuppliedEquivariantFiniteFredholmDatum_action
    (act : G2IntegratedAction G) :
    (canonicalNativeSuppliedEquivariantFiniteFredholmDatum act).action =
      nativeIntegratedAction act := rfl

/-- Canonical native datum attached to the supplied finite group action. -/
def canonicalNativeIntegratedActionDatum
    (act : G2IntegratedAction G) : NativeIntegratedActionDatum act where
  action := nativeIntegratedAction act
  action_eq := rfl
  commutes_hodge := nativeIntegratedAction_commutes_hodge act
  commutes_chirality := nativeIntegratedAction_commutes_chirality act
  commutes_normalized_dirac := nativeIntegratedAction_commutes_normalized_dirac act

theorem nativeIntegratedAction_inverse_comp
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g⁻¹).comp (nativeIntegratedAction act g) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [nativeIntegratedAction_apply, nativeIntegratedAction_apply]
  rw [← nativeContinuous_mul, ← Units.val_mul, ← act.U.map_mul,
    inv_mul_cancel, map_one]
  exact nativeContinuous_one

theorem nativeIntegratedAction_comp_inverse
    (act : G2IntegratedAction G) (g : G) :
    (nativeIntegratedAction act g).comp (nativeIntegratedAction act g⁻¹) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [nativeIntegratedAction_apply, nativeIntegratedAction_apply]
  rw [← nativeContinuous_mul, ← Units.val_mul, ← act.U.map_mul,
    mul_inv_cancel, map_one]
  exact nativeContinuous_one

noncomputable def nativeIntegratedActionEquiv
    (act : G2IntegratedAction G) (g : G) :
    NativeSpinorCarrier ≃L[ℝ] NativeSpinorCarrier where
  toFun := nativeIntegratedAction act g
  invFun := nativeIntegratedAction act g⁻¹
  map_add' := (nativeIntegratedAction act g).map_add
  map_smul' := (nativeIntegratedAction act g).map_smul
  left_inv := by
    intro x
    have h := congrArg (fun T : NativeSpinorCLM => T x)
      (nativeIntegratedAction_inverse_comp act g)
    simpa [ContinuousLinearMap.comp_apply] using h
  right_inv := by
    intro x
    have h := congrArg (fun T : NativeSpinorCLM => T x)
      (nativeIntegratedAction_comp_inverse act g)
    simpa [ContinuousLinearMap.comp_apply] using h
  continuous_toFun := (nativeIntegratedAction act g).cont
  continuous_invFun := (nativeIntegratedAction act g⁻¹).cont

@[simp] theorem nativeIntegratedActionEquiv_apply
    (act : G2IntegratedAction G) (g : G) (x : NativeSpinorCarrier) :
    nativeIntegratedActionEquiv act g x = nativeIntegratedAction act g x := rfl

theorem nativeIntegratedActionEquiv_trans
    (act : G2IntegratedAction G) (g h : G) :
    (nativeIntegratedActionEquiv act h).trans
        (nativeIntegratedActionEquiv act g) =
      nativeIntegratedActionEquiv act (g * h) := by
  apply ContinuousLinearEquiv.ext
  apply funext
  intro x
  change nativeIntegratedAction act g (nativeIntegratedAction act h x) =
    nativeIntegratedAction act (g * h) x
  simpa [ContinuousLinearMap.comp_apply] using
    (congrArg (fun T : NativeSpinorCLM => T x)
      (map_mul (nativeIntegratedAction act) g h)).symm

theorem nativeIntegratedAction_bijective
    (act : G2IntegratedAction G) (g : G) :
    Function.Bijective (nativeIntegratedAction act g) := by
  constructor
  · intro x y hxy
    calc
      x = nativeIntegratedAction act g⁻¹ (nativeIntegratedAction act g x) := by
        have h := congrArg (fun T : NativeSpinorCLM => T x)
          (nativeIntegratedAction_inverse_comp act g)
        simpa [ContinuousLinearMap.comp_apply] using h.symm
      _ = nativeIntegratedAction act g⁻¹ (nativeIntegratedAction act g y) := by
        rw [hxy]
      _ = y := by
        have h := congrArg (fun T : NativeSpinorCLM => T y)
          (nativeIntegratedAction_inverse_comp act g)
        simpa [ContinuousLinearMap.comp_apply] using h
  · intro y
    refine ⟨nativeIntegratedAction act g⁻¹ y, ?_⟩
    have h := congrArg (fun T : NativeSpinorCLM => T y)
      (nativeIntegratedAction_comp_inverse act g)
    simpa [ContinuousLinearMap.comp_apply] using h

theorem nativeIntegratedAction_preserves_projectorPlus
    (act : G2IntegratedAction G) (g : G) (x : NativeSpinorCarrier) :
    nativeChiralProjectorPlus (nativeIntegratedAction act g x) =
      nativeIntegratedAction act g (nativeChiralProjectorPlus x) := by
  have h := congrArg (fun T : NativeSpinorCLM => T x)
    (nativeIntegratedAction_commutes_projectorPlus act g)
  simpa [ContinuousLinearMap.comp_apply] using h.symm

theorem nativeIntegratedAction_preserves_projectorMinus
    (act : G2IntegratedAction G) (g : G) (x : NativeSpinorCarrier) :
    nativeChiralProjectorMinus (nativeIntegratedAction act g x) =
      nativeIntegratedAction act g (nativeChiralProjectorMinus x) := by
  have h := congrArg (fun T : NativeSpinorCLM => T x)
    (nativeIntegratedAction_commutes_projectorMinus act g)
  simpa [ContinuousLinearMap.comp_apply] using h.symm

theorem nativeIntegratedAction_preserves_plus_sector
    (act : G2IntegratedAction G) (g : G) (x : NativeSpinorCarrier)
    (hx : nativeChiralProjectorPlus x = x) :
    nativeChiralProjectorPlus (nativeIntegratedAction act g x) =
      nativeIntegratedAction act g x := by
  rw [nativeIntegratedAction_preserves_projectorPlus act g x, hx]

theorem nativeIntegratedAction_preserves_minus_sector
    (act : G2IntegratedAction G) (g : G) (x : NativeSpinorCarrier)
    (hx : nativeChiralProjectorMinus x = x) :
    nativeChiralProjectorMinus (nativeIntegratedAction act g x) =
      nativeIntegratedAction act g x := by
  rw [nativeIntegratedAction_preserves_projectorMinus act g x, hx]

end InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
