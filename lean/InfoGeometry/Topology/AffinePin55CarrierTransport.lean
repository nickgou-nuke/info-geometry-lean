import InfoGeometry.Topology.Pin55CarrierHomeomorph
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AffinePin55TopologicalGroup

/-!
# Transport from the opposite split Pin carrier to the affine carrier

The opposite carrier acts on the same quadratic vector space by transport
through the explicit carrier homeomorphism.  The resulting semidirect
product is a separate native carrier; it is mapped to the existing affine
`Pin⁺` carrier by a genuine semidirect-product homomorphism.
-/

noncomputable section

namespace InfoGeometry.Topology.Pin55TopologicalGroups

open InfoGeometry.Canonical.AffinePin55Cover
open InfoGeometry.Topology.AffinePin55TopologicalGroup
open InfoGeometry.Clifford.Clifford55

noncomputable def pinMinus55Action :
    PinMinus55 →* MulAut (Multiplicative V55) :=
  realSplitPinAction.comp pinMinus55ToPlus

theorem pinMinus55Action_apply (g : PinMinus55) (v : Multiplicative V55) :
    pinMinus55Action g v = realSplitPinAction (pinMinus55ToPlus g) v :=
  rfl

theorem pinMinus55Action_continuous :
    Continuous (fun p : PinMinus55 × Multiplicative V55 =>
      pinMinus55Action p.1 p.2) := by
  have hpair : Continuous (fun p : PinMinus55 × Multiplicative V55 =>
      (pinMinus55ToPlus p.1, p.2)) :=
    pinMinus55HomeomorphPlus.continuous_toFun.comp continuous_fst |>.prodMk
      continuous_snd
  simpa only [Function.comp_apply, pinMinus55Action_apply] using
    realSplitPinAction_continuous.comp hpair

abbrev AffinePinMinus55Native :=
  Multiplicative V55 ⋊[pinMinus55Action] PinMinus55

def affinePinMinus55ToPlus :
    AffinePinMinus55Native →* AffinePin55Native :=
  SemidirectProduct.map (MonoidHom.id _) pinMinus55ToPlus (by
    intro g
    apply MonoidHom.ext
    intro v
    rfl)

theorem affinePinMinus55ToPlus_left (x : AffinePinMinus55Native) :
    (affinePinMinus55ToPlus x).left = x.left := by
  rfl

theorem affinePinMinus55ToPlus_right (x : AffinePinMinus55Native) :
    (affinePinMinus55ToPlus x).right = pinMinus55ToPlus x.right := by
  rfl

noncomputable instance affinePinMinus55_topologicalSpace :
    TopologicalSpace AffinePinMinus55Native :=
  TopologicalSpace.induced (fun x : AffinePinMinus55Native =>
    (x.left, x.right)) inferInstance

private theorem affinePinMinus55_coordinate_continuous :
    Continuous (fun x : AffinePinMinus55Native => (x.left, x.right)) :=
  continuous_induced_dom

theorem affinePinMinus55ToPlus_continuous :
    Continuous (affinePinMinus55ToPlus :
      AffinePinMinus55Native → AffinePin55Native) := by
  apply continuous_induced_rng.mpr
  have hleft : Continuous (fun x : AffinePinMinus55Native => x.left) :=
    continuous_fst.comp affinePinMinus55_coordinate_continuous
  have hright : Continuous (fun x : AffinePinMinus55Native =>
      pinMinus55ToPlus x.right) :=
    pinMinus55HomeomorphPlus.continuous_toFun.comp
      (continuous_snd.comp affinePinMinus55_coordinate_continuous)
  simpa only [Function.comp_apply,
    affinePinMinus55ToPlus_left, affinePinMinus55ToPlus_right] using
    hleft.prodMk hright

set_option maxHeartbeats 800000 in
theorem affinePinMinus55_isTopologicalGroup_of_continuous_action :
    @IsTopologicalGroup AffinePinMinus55Native
      affinePinMinus55_topologicalSpace inferInstance := by
  letI : TopologicalSpace AffinePinMinus55Native :=
    affinePinMinus55_topologicalSpace
  let e : AffinePinMinus55Native ≃ₜ
      Multiplicative V55 × PinMinus55 :=
    { SemidirectProduct.equivProd with
      continuous_toFun := continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr continuous_id }
  let coordMul :
      (Multiplicative V55 × PinMinus55) ×
        (Multiplicative V55 × PinMinus55) →
        (Multiplicative V55 × PinMinus55) :=
    fun p =>
      (p.1.1 * (pinMinus55Action p.1.2) p.2.1, p.1.2 * p.2.2)
  let coordInv : Multiplicative V55 × PinMinus55 →
      Multiplicative V55 × PinMinus55 :=
    fun p =>
      ((pinMinus55Action p.2⁻¹) (p.1⁻¹), p.2⁻¹)
  have h_action' : Continuous (fun p :
      (Multiplicative V55 × PinMinus55) ×
        (Multiplicative V55 × PinMinus55) =>
      (pinMinus55Action p.1.2) p.2.1) := by
    simpa only [Function.comp_apply] using
      pinMinus55Action_continuous.comp
        (continuous_fst.snd.prodMk continuous_snd.fst)
  have h_coordMul : Continuous coordMul := by
    dsimp [coordMul]
    exact (continuous_fst.fst.mul h_action').prodMk
      (continuous_fst.snd.mul continuous_snd.snd)
  have h_action_inv : Continuous (fun p :
      Multiplicative V55 × PinMinus55 =>
      (pinMinus55Action p.2⁻¹) (p.1⁻¹)) := by
    simpa only [Function.comp_apply] using
      pinMinus55Action_continuous.comp
        (continuous_snd.inv.prodMk continuous_fst.inv)
  have h_coordInv : Continuous coordInv := by
    dsimp [coordInv]
    exact h_action_inv.prodMk continuous_snd.inv
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.mpr
    rw [show (fun x : AffinePinMinus55Native =>
        (x.left, x.right)) ∘ (fun p :
          AffinePinMinus55Native × AffinePinMinus55Native => p.1 * p.2) =
      coordMul ∘ (Homeomorph.prodCongr e e) by
        funext p
        rfl]
    exact h_coordMul.comp (Homeomorph.prodCongr e e).continuous_toFun
  · apply continuous_induced_rng.mpr
    rw [show (fun x : AffinePinMinus55Native =>
        (x.left, x.right)) ∘ (fun p : AffinePinMinus55Native => p⁻¹) =
      coordInv ∘ e by
        funext p
        rfl]
    exact h_coordInv.comp e.continuous_toFun

noncomputable instance affinePinMinus55_topologicalGroup :
    IsTopologicalGroup AffinePinMinus55Native := by
  exact affinePinMinus55_isTopologicalGroup_of_continuous_action

end InfoGeometry.Topology.Pin55TopologicalGroups
