import proofs.KleinSixStateBundleOrbitEquiv

/-!
# Topological identification of the six-state bundle and orbit quotient

The algebraic equivalence is upgraded locally in the covering charts.  No
global continuity of the chosen section is assumed.
-/

noncomputable section
namespace KleinSixStateBundleOrbitHomeomorph

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas KleinSixStateBundle TwoSheetThreeColorWeyl
open KleinSixStateAssociatedQuotient KleinSixStateVectorBundleCore
open KleinSixStateBundleOrbitEquiv

abbrev Base := KleinBrillouinQuotient
abbrev State := Fin 2 × Fin 3 → ℂ

private theorem chartCoord_eq (i : Base) (k : BrillouinTorus)
    (hi : quotientMap k ∈ (coverTriv i).baseSet) :
    ((coverTriv i) k).2 =
      coverCoord k + deckTransition (quotientMap k) i (quotientMap k) := by
  have hk : k ∈ (coverTriv (quotientMap k)).source := by
    rw [(coverTriv (quotientMap k)).mem_source]
    exact mem_coverTriv_baseSet (quotientMap k)
  have h := (coverTriv (quotientMap k)).coordChange_apply_snd
    (coverTriv i) hk
  change (coverTriv (quotientMap k)).coordChange (coverTriv i)
      (quotientMap k) (coverCoord k) = ((coverTriv i) k).2 at h
  rw [injective_deck2_eq_add_apply_zero
    ((coverTriv (quotientMap k)).coordChange (coverTriv i) (quotientMap k))
    ((coverTriv (quotientMap k)).coordChangeHomeomorph (coverTriv i)
      (mem_coverTriv_baseSet (quotientMap k)) hi).injective
    (coverCoord k)] at h
  exact h.symm

private theorem local_coordinate_representative (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i : Base)
    (k : BrillouinTorus) (v : State)
    (hi : quotientMap k ∈ (coverTriv i).baseSet) :
    ((kleinSixStateVectorBundleCore omega homega).localTriv i
      (⟨quotientMap k, deckFiberMap (coverCoord k) v⟩ :
        (kleinSixStateVectorBundleCore omega homega).TotalSpace)).2 =
      deckFiberMap (((coverTriv i) k).2) v := by
  rw [VectorBundleCore.localTriv_apply]
  change deckFiberMap (deckTransition (quotientMap k) i (quotientMap k))
      (deckFiberMap (coverCoord k) v) = _
  rw [← deckFiberMap_add omega homega, ← chartCoord_eq i k hi]

private theorem continuousOn_fixed_chart_coordinate (i : Base) :
    ContinuousOn
      (fun p : BrillouinTorus × State ↦
        deckFiberMap (((coverTriv i) p.1).2) p.2)
      ((coverTriv i).source ×ˢ Set.univ) := by
  have hc : ContinuousOn
      (fun p : BrillouinTorus × State ↦ deckFiberMap (((coverTriv i) p.1).2))
      ((coverTriv i).source ×ˢ Set.univ) :=
    continuous_deckFiberMap.comp_continuousOn
      (continuous_snd.comp_continuousOn
        ((coverTriv i).toOpenPartialHomeomorph.continuousOn.comp
          continuousOn_fst (fun p hp ↦ hp.1)))
  have hv : ContinuousOn (fun p : BrillouinTorus × State ↦ p.2)
      ((coverTriv i).source ×ˢ Set.univ) := continuous_snd.continuousOn
  exact isBoundedBilinearMap_apply.continuous.comp_continuousOn
    (hc.prodMk hv)

private theorem representativeToCore_continuous (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (fun p : BrillouinTorus × State ↦
      (⟨quotientMap p.1, deckFiberMap (coverCoord p.1) p.2⟩ :
        (kleinSixStateVectorBundleCore omega homega).TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · exact quotientMap_continuous.continuousAt.comp continuousAt_fst
  · let i : Base := quotientMap p.1
    change ContinuousAt
      (fun q : BrillouinTorus × State ↦
        (((kleinSixStateVectorBundleCore omega homega).localTriv i)
          (⟨quotientMap q.1, deckFiberMap (coverCoord q.1) q.2⟩ :
            (kleinSixStateVectorBundleCore omega homega).TotalSpace)).2) p
    have hp : p ∈ (coverTriv i).source ×ˢ (Set.univ : Set State) := by
      refine ⟨?_, Set.mem_univ _⟩
      rw [(coverTriv i).mem_source]
      exact mem_coverTriv_baseSet i
    have hopen : IsOpen ((coverTriv i).source ×ˢ (Set.univ : Set State)) :=
      (coverTriv i).open_source.prod isOpen_univ
    have hfixed : ContinuousAt
        (fun q : BrillouinTorus × State ↦
          deckFiberMap (((coverTriv i) q.1).2) q.2) p :=
      (continuousOn_fixed_chart_coordinate i).continuousAt (hopen.mem_nhds hp)
    have hlocal : Filter.Eventually (fun q : BrillouinTorus × State ↦
        (((kleinSixStateVectorBundleCore omega homega).localTriv i)
          (⟨quotientMap q.1, deckFiberMap (coverCoord q.1) q.2⟩ :
            (kleinSixStateVectorBundleCore omega homega).TotalSpace)).2 =
          deckFiberMap (((coverTriv i) q.1).2) q.2) (nhds p) := by
      filter_upwards [hopen.mem_nhds hp] with q hq
      apply local_coordinate_representative omega homega i q.1 q.2
      rw [← (coverTriv i).mem_source]
      exact hq.1
    exact hfixed.congr_of_eventuallyEq hlocal

theorem orbitToCore_continuous (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (orbitToCore omega homega) := by
  apply continuous_quot_lift
  exact representativeToCore_continuous omega homega

private def chartSection (i : Base) (b : Base) : BrillouinTorus :=
  (coverTriv i).toOpenPartialHomeomorph.symm (b, (0 : Deck2))

private def localOrbit (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (i : Base) (p : Base × State) : AssociatedSixState omega homega :=
  totalQuotientMap omega homega (chartSection i p.1, p.2)

private theorem chartSection_mem_source (i b : Base)
    (hb : b ∈ (coverTriv i).baseSet) :
    chartSection i b ∈ (coverTriv i).source := by
  rw [(coverTriv i).mem_source]
  unfold chartSection
  rw [(coverTriv i).proj_symm_apply' hb]
  exact hb

private theorem chartSection_proj (i b : Base)
    (hb : b ∈ (coverTriv i).baseSet) :
    quotientMap (chartSection i b) = b :=
  (coverTriv i).proj_symm_apply' hb

private theorem chartSection_coord (i b : Base)
    (hb : b ∈ (coverTriv i).baseSet) :
    ((coverTriv i) (chartSection i b)).2 = 0 := by
  exact congrArg Prod.snd ((coverTriv i).apply_symm_apply' hb)

private theorem representative_chart_in_local_coordinates (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i b : Base) (v : State)
    (hb : b ∈ (coverTriv i).baseSet) :
    ((kleinSixStateVectorBundleCore omega homega).localTriv i)
      (⟨quotientMap (chartSection i b),
        deckFiberMap (coverCoord (chartSection i b)) v⟩ :
          (kleinSixStateVectorBundleCore omega homega).TotalSpace) = (b, v) := by
  apply Prod.ext
  · rw [(kleinSixStateVectorBundleCore omega homega).localTriv_apply,
      chartSection_proj i b hb]
  · rw [local_coordinate_representative omega homega i (chartSection i b) v]
    · rw [chartSection_coord i b hb, deckFiberMap_zero]
      rfl
    · simpa [chartSection_proj i b hb] using hb

private theorem coreToOrbit_eq_localOrbit (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i : Base)
    (p : (kleinSixStateVectorBundleCore omega homega).TotalSpace)
    (hp : p.1 ∈ (coverTriv i).baseSet) :
    coreToOrbit omega homega p =
      localOrbit omega homega i
        ((kleinSixStateVectorBundleCore omega homega).localTriv i p) := by
  apply (Function.LeftInverse.injective (coreToOrbit_orbitToCore omega homega))
  rw [orbitToCore_coreToOrbit]
  symm
  change (⟨quotientMap (chartSection i p.1),
      deckFiberMap (coverCoord (chartSection i p.1))
        (((kleinSixStateVectorBundleCore omega homega).localTriv i p).2)⟩ :
      (kleinSixStateVectorBundleCore omega homega).TotalSpace) = p
  apply ((kleinSixStateVectorBundleCore omega homega).localTriv i).toPartialEquiv.injOn
  · rw [(kleinSixStateVectorBundleCore omega homega).localTriv_apply,
      chartSection_proj i p.1 hp]
    exact hp
  · exact hp
  · change ((kleinSixStateVectorBundleCore omega homega).localTriv i)
        (⟨quotientMap (chartSection i p.1),
          deckFiberMap (coverCoord (chartSection i p.1))
            (((kleinSixStateVectorBundleCore omega homega).localTriv i p).2)⟩ :
          (kleinSixStateVectorBundleCore omega homega).TotalSpace) =
        (kleinSixStateVectorBundleCore omega homega).localTriv i p
    rw [representative_chart_in_local_coordinates omega homega i p.1 _ hp]
    apply Prod.ext
    · exact ((kleinSixStateVectorBundleCore omega homega).localTriv i).coe_fst'
        hp |>.symm
    · rfl

private theorem localOrbit_continuousAt (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i : Base) (p : Base × State)
    (hp : p.1 ∈ (coverTriv i).baseSet) :
    ContinuousAt (localOrbit omega homega i) p := by
  have ht : (p.1, (0 : Deck2)) ∈ (coverTriv i).target := by
    rw [(coverTriv i).mem_target]
    exact hp
  have hpair : ContinuousAt (fun b : Base ↦ (b, (0 : Deck2))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hs : ContinuousAt (chartSection i) p.1 := by
    unfold chartSection
    simpa only [Function.comp_apply] using
      (ContinuousAt.comp (f := fun b : Base ↦ (b, (0 : Deck2)))
        ((coverTriv i).toOpenPartialHomeomorph.continuousAt_symm ht) hpair)
  have htotal : ContinuousAt
      (fun q : Base × State ↦ (chartSection i q.1, q.2)) p :=
    (hs.comp continuousAt_fst).prodMk continuousAt_snd
  simpa only [localOrbit, Function.comp_apply] using
    continuous_quot_mk.continuousAt.comp htotal

theorem coreToOrbit_continuous (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (coreToOrbit omega homega) := by
  rw [continuous_iff_continuousAt]
  intro p
  let i : Base := p.1
  let e := (kleinSixStateVectorBundleCore omega homega).localTriv i
  have hp : p.1 ∈ e.baseSet := mem_coverTriv_baseSet p.1
  apply e.continuousAt_of_comp_right hp
  have hep : ContinuousAt (localOrbit omega homega i) (e p) :=
    localOrbit_continuousAt omega homega i (e p)
      ((e.coe_fst' hp) ▸ hp)
  have heopen : IsOpen e.target := e.open_target
  have heptarget : e p ∈ e.target := e.map_source hp
  have heq : Filter.Eventually (fun q : Base × State ↦
      (coreToOrbit omega homega ∘ e.toPartialEquiv.symm) q =
        localOrbit omega homega i q) (nhds (e p)) := by
    filter_upwards [heopen.mem_nhds heptarget] with q hq
    have hbase : q.1 ∈ e.baseSet := by
      rw [e.mem_target] at hq
      exact hq
    have hsymm : (e.toPartialEquiv.symm q).1 ∈ e.baseSet := by
      have hproj : Bundle.TotalSpace.proj (e.toPartialEquiv.symm q) = q.1 :=
        e.proj_symm_apply hq
      exact hproj.symm ▸ hbase
    rw [Function.comp_apply,
      coreToOrbit_eq_localOrbit omega homega i (e.toPartialEquiv.symm q) hsymm]
    change localOrbit omega homega i (e (e.toPartialEquiv.symm q)) =
      localOrbit omega homega i q
    exact congrArg (localOrbit omega homega i) (e.apply_symm_apply hq)
  exact hep.congr_of_eventuallyEq heq

/-- The literal simultaneous-glide quotient is homeomorphic to the total
space of the native Mathlib vector-bundle core. -/
def bundleTotalOrbitHomeomorph (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    (kleinSixStateVectorBundleCore omega homega).TotalSpace ≃ₜ
      AssociatedSixState omega homega where
  toEquiv := bundleTotalOrbitEquiv omega homega
  continuous_toFun := coreToOrbit_continuous omega homega
  continuous_invFun := orbitToCore_continuous omega homega

end KleinSixStateBundleOrbitHomeomorph
end noncomputable section
