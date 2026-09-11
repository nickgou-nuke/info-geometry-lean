import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Group.Basic
import InfoGeometry.Canonical.AffinePin55Cover
import InfoGeometry.Topology.Pin55TopologicalGroups
import InfoGeometry.Topology.Pin55ContinuityLemmas

/-!
# The topological affine split-Pin group

The algebraic carrier `AffinePin55Native` is the native Mathlib semidirect
product.  Its topology is transported from the product of the translation and
split-Pin factors.  The action is proved jointly continuous from the actual
Clifford conjugation formula; it is not declared continuous by a typeclass
placeholder.
-/

noncomputable section

namespace InfoGeometry.Topology.AffinePin55TopologicalGroup

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Topology.Pin55TopologicalGroups
open InfoGeometry.Canonical.AffinePin55Cover

abbrev AffinePin55 := AffinePin55Native

private theorem range_action_continuous :
    Continuous (fun p : realSplitPin55 × V55 =>
      (⟨realSplitPinTwistedAdj p.1 p.2,
        realSplitPinTwistedAdj_mem_ι_range p.1 p.2⟩ : LinearMap.range ι55)) := by
  apply Continuous.subtype_mk
  exact InfoGeometry.Topology.Pin55ContinuityLemmas.continuous_realSplitPin_twisted_adj

theorem realSplitPinAction_continuous :
    Continuous (fun p : realSplitPin55 × Multiplicative V55 =>
      realSplitPinAction p.1 p.2) := by
  have hR : Continuous (fun p : realSplitPin55 × V55 =>
      realSplitPinTwistedRangeEndomorphism p.1 (ι55RangeEquiv p.2)) := by
    simpa only [realSplitPinTwistedRangeEndomorphism, LinearMap.codRestrict_apply] using
      range_action_continuous
  have hS : Continuous (fun p : realSplitPin55 × V55 =>
      ι55RangeEquiv.symm
        (realSplitPinTwistedRangeEndomorphism p.1 (ι55RangeEquiv p.2))) := by
    exact (LinearMap.continuous_of_finiteDimensional
      ι55RangeEquiv.symm.toLinearMap).comp hR
  have hA : Continuous (fun p : realSplitPin55 × V55 =>
      realSplitPinTwistedAction p.1 p.2) := by
    simpa only [realSplitPinTwistedAction] using hS
  simpa only [realSplitPinAction, nativeOrthogonalAction,
    realSplitPinOrthogonalAction] using
    hA.comp (continuous_fst.prodMk continuous_snd)

noncomputable instance affinePin55_topologicalSpace : TopologicalSpace AffinePin55 :=
  TopologicalSpace.induced (fun x : AffinePin55 => (x.left, x.right)) inferInstance

private theorem affinePin55_coordinate_continuous :
    Continuous (fun x : AffinePin55 => (x.left, x.right)) :=
  continuous_induced_dom

private theorem affinePin55_left_continuous :
    Continuous (fun x : AffinePin55 => x.left) :=
  continuous_fst.comp affinePin55_coordinate_continuous

private theorem affinePin55_right_continuous :
    Continuous (fun x : AffinePin55 => x.right) :=
  continuous_snd.comp affinePin55_coordinate_continuous

set_option maxHeartbeats 800000 in
instance instIsTopologicalGroupAffinePin55 : IsTopologicalGroup AffinePin55 where
  continuous_mul := by
    apply (continuous_induced_rng).2
    have hpair : Continuous (fun p : AffinePin55 × AffinePin55 =>
        (p.1.right, p.2.left)) :=
      Continuous.prodMk
        (affinePin55_right_continuous.comp continuous_fst)
        (affinePin55_left_continuous.comp continuous_snd)
    have hact' := realSplitPinAction_continuous.comp hpair
    have hact : Continuous (fun p : AffinePin55 × AffinePin55 =>
        realSplitPinAction p.1.right p.2.left) := by
      simpa only [Function.comp_apply] using hact'
    have hmul : Continuous (fun p : Multiplicative V55 × Multiplicative V55 =>
        p.1 * p.2) := continuous_mul
    have hleft : Continuous (fun p : AffinePin55 × AffinePin55 =>
        p.1.left * realSplitPinAction p.1.right p.2.left) :=
      by
        simpa only [Function.comp_apply] using
          hmul.comp
            (Continuous.prodMk
              (affinePin55_left_continuous.comp continuous_fst) hact)
    have hright : Continuous (fun p : AffinePin55 × AffinePin55 =>
        p.1.right * p.2.right) :=
      by
        simpa only [Function.comp_apply] using
          have hpinmul : Continuous (fun p : realSplitPin55 × realSplitPin55 =>
              p.1 * p.2) := continuous_mul
          hpinmul.comp
            (Continuous.prodMk
              (affinePin55_right_continuous.comp continuous_fst)
              (affinePin55_right_continuous.comp continuous_snd))
    simpa only [Function.comp_apply, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right] using hleft.prodMk hright
  continuous_inv := by
    apply (continuous_induced_rng).2
    have hleftInv : Continuous (fun x : AffinePin55 => x.left⁻¹) :=
      continuous_inv.comp affinePin55_left_continuous
    have hrightInv : Continuous (fun x : AffinePin55 => x.right⁻¹) :=
      continuous_inv.comp affinePin55_right_continuous
    have hact : Continuous (fun x : AffinePin55 =>
        realSplitPinAction x.right⁻¹ x.left⁻¹) :=
      by
        simpa only [Function.comp_apply] using
          realSplitPinAction_continuous.comp (Continuous.prodMk hrightInv hleftInv)
    simpa only [Function.comp_apply, SemidirectProduct.inv_left,
      SemidirectProduct.inv_right] using hact.prodMk hrightInv

end InfoGeometry.Topology.AffinePin55TopologicalGroup
