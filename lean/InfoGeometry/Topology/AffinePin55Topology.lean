import Mathlib.Topology.Algebra.Group.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.AffinePin55Cover
import InfoGeometry.Topology.Pin55TopologicalGroups

noncomputable section

namespace InfoGeometry.Topology.AffinePin55Topology

open InfoGeometry.Canonical.AffinePin55Cover
open InfoGeometry.Clifford.Clifford55

theorem continuous_realSplitPin_action_fixed (g : realSplitPin55) :
    Continuous (fun x : V55 =>
      ((realSplitPinAction g) (Multiplicative.ofAdd x)).toAdd) := by
  change Continuous (fun x : V55 =>
    (realSplitPinOrthogonalAction g : V55 ≃ₗ[ℝ] V55) x)
  exact LinearMap.continuous_of_finiteDimensional _

theorem continuous_realSplitPin_twistedAdj :
    Continuous (fun p : realSplitPin55 × V55 =>
      realSplitPinTwistedAdj p.1 p.2) := by
  have hg : Continuous (fun g : realSplitPin55 =>
      ((g : Cl55ˣ) : Cl55)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hginv : Continuous (fun g : realSplitPin55 =>
      (↑((g : Cl55ˣ)⁻¹) : Cl55)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hi : Continuous (fun x : Cl55 =>
      CliffordAlgebra.involute (Q := Q55) x) :=
    (LinearMap.continuous_of_finiteDimensional
      (CliffordAlgebra.involute (Q := Q55)).toLinearMap)
  have hι : Continuous (ι55 : V55 → Cl55) :=
    LinearMap.continuous_of_finiteDimensional _
  dsimp [realSplitPinTwistedAdj]
  exact ((hi.comp (hg.comp continuous_fst)).mul
    (hι.comp continuous_snd)).mul
      (hginv.comp continuous_fst)

theorem continuous_realSplitPin_action :
    Continuous (fun p : realSplitPin55 × V55 =>
      realSplitPinTwistedAction p.1 p.2) := by
  letI : T2Space (LinearMap.range (ι55)) :=
    T2Space.of_injective_continuous
      (fun _ _ h => Subtype.ext h) continuous_subtype_val
  have h_range_inv : Continuous (ι55RangeEquiv.symm :
      LinearMap.range (ι55) → V55) :=
    LinearMap.continuous_of_finiteDimensional ι55RangeEquiv.symm.toLinearMap
  have h_range : Continuous (fun p : realSplitPin55 × V55 =>
      (⟨realSplitPinTwistedAdj p.1 p.2,
        realSplitPinTwistedAdj_mem_ι_range p.1 p.2⟩ : LinearMap.range (ι55))) :=
    continuous_realSplitPin_twistedAdj.subtype_mk _
  have h := h_range_inv.comp h_range
  apply h.congr
  intro p
  apply ι55RangeEquiv.injective
  change ι55RangeEquiv
      (realSplitPinTwistedAction p.1 p.2) = _
  change ι55RangeEquiv
      (ι55RangeEquiv.symm
        (realSplitPinTwistedRangeEndomorphism p.1
          (ι55RangeEquiv p.2))) = _
  rw [ι55RangeEquiv.apply_symm_apply]
  apply Subtype.ext
  change realSplitPinTwistedAdj p.1 p.2 =
    ι55 (realSplitPinTwistedAction p.1 p.2)
  exact (realSplitPinTwistedAction_apply_ι p.1 p.2).symm

def affinePin55Topology : TopologicalSpace AffinePin55Native :=
  TopologicalSpace.induced SemidirectProduct.equivProd inferInstance

set_option maxHeartbeats 800000 in
theorem affinePin55_isTopologicalGroup_of_continuous_action
    (h_action : Continuous (fun p : realSplitPin55 × Multiplicative V55 =>
      (realSplitPinAction p.1) p.2)) :
    @IsTopologicalGroup AffinePin55Native affinePin55Topology inferInstance := by
  letI : TopologicalSpace AffinePin55Native := affinePin55Topology
  let e : AffinePin55Native ≃ₜ Multiplicative V55 × realSplitPin55 :=
    { SemidirectProduct.equivProd with
      continuous_toFun := continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr continuous_id }
  let coordMul :
      (Multiplicative V55 × realSplitPin55) ×
        (Multiplicative V55 × realSplitPin55) →
        (Multiplicative V55 × realSplitPin55) :=
    fun p =>
      (p.1.1 * (realSplitPinAction p.1.2) p.2.1, p.1.2 * p.2.2)
  let coordInv : Multiplicative V55 × realSplitPin55 →
      Multiplicative V55 × realSplitPin55 :=
    fun p =>
      ((realSplitPinAction p.2⁻¹) (p.1⁻¹), p.2⁻¹)
  have h_action' : Continuous (fun p :
      (Multiplicative V55 × realSplitPin55) ×
        (Multiplicative V55 × realSplitPin55) =>
    (realSplitPinAction p.1.2) p.2.1) := by
    simpa only [Function.comp_apply] using
      h_action.comp (continuous_fst.snd.prodMk continuous_snd.fst)
  have h_coordMul : Continuous coordMul := by
    dsimp [coordMul]
    exact (continuous_fst.fst.mul h_action').prodMk
      (continuous_fst.snd.mul continuous_snd.snd)
  have h_action_inv : Continuous (fun p :
      Multiplicative V55 × realSplitPin55 =>
      (realSplitPinAction p.2⁻¹) (p.1⁻¹)) := by
    simpa only [Function.comp_apply] using
      h_action.comp (continuous_snd.inv.prodMk continuous_fst.inv)
  have h_coordInv : Continuous coordInv := by
    dsimp [coordInv]
    exact h_action_inv.prodMk continuous_snd.inv
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.mpr
    rw [show SemidirectProduct.equivProd ∘ (fun p :
      AffinePin55Native × AffinePin55Native => p.1 * p.2) =
      coordMul ∘ (Homeomorph.prodCongr e e) by
      funext p
      rfl]
    exact h_coordMul.comp (Homeomorph.prodCongr e e).continuous_toFun
  · apply continuous_induced_rng.mpr
    rw [show SemidirectProduct.equivProd ∘ (fun p :
      AffinePin55Native => p⁻¹) =
      coordInv ∘ e by
      funext p
      rfl]
    exact h_coordInv.comp e.continuous_toFun

theorem affinePin55_isTopologicalGroup :
    @IsTopologicalGroup AffinePin55Native affinePin55Topology inferInstance := by
  apply affinePin55_isTopologicalGroup_of_continuous_action
  change Continuous (fun p : realSplitPin55 × V55 =>
    realSplitPinTwistedAction p.1 p.2)
  exact continuous_realSplitPin_action

instance affinePin55_topologicalSpace : TopologicalSpace AffinePin55Native :=
  affinePin55Topology

instance affinePin55_topologicalGroup : IsTopologicalGroup AffinePin55Native := by
  exact affinePin55_isTopologicalGroup

end InfoGeometry.Topology.AffinePin55Topology
