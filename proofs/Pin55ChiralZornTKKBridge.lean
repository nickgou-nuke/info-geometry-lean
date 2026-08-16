import proofs.Clifford55AnomalyOSP
import proofs.ArtinCentralizerMonodromy
import proofs.Pin55CartanDecomposition
import proofs.PinO55GlideReflection
import proofs.ChiralCausalConeTKKBridge
import proofs.ZornChiralBridge
import proofs.ZornParavectorNullspace
import InfoGeometry.Canonical.ZornTrialityTKKBridge

noncomputable section

namespace Pin55ChiralZornTKKBridge

open Pin55CartanDecomposition
open ChiralCausalConeTKKBridge
open ZornChiralBridge
open ZornTrialityTKKBridge
open Clifford55AnomalyOSP
open ArtinCentralizerMonodromy
open PinO55GlideReflection

/-- Local carrier map from the canonical Zorn paravector coordinates to the
chiral `2×2` matrix carrier.  This is the concrete bridge object used in the
summary below. -/
def bridgeCarrierMap (X : ZornParavectorNullspace.Zorn) : ChiralCausalCone.M2C :=
  !![X.a, X.u 0; X.v 0, X.b]

/-! ### The restricted four-coordinate slice

`bridgeCarrierMap` is not a representation of the full Zorn carrier.  On the
slice where the last two coordinates of both vector lanes vanish, the cross
products vanish and the map becomes multiplicative. -/

def bridgeSlice (X : ZornParavectorNullspace.Zorn) : Prop :=
  X.u 1 = 0 ∧ X.u 2 = 0 ∧ X.v 1 = 0 ∧ X.v 2 = 0

abbrev RestrictedZorn :=
  {X : ZornParavectorNullspace.Zorn // bridgeSlice X}

theorem bridgeSlice_zornMul
    {X Y : ZornParavectorNullspace.Zorn}
    (hX : bridgeSlice X) (hY : bridgeSlice Y) :
    bridgeSlice (ZornParavectorNullspace.zornMul X Y) := by
  rcases hX with ⟨huX1, huX2, hvX1, hvX2⟩
  rcases hY with ⟨huY1, huY2, hvY1, hvY2⟩
  constructor
  · simp [ZornParavectorNullspace.zornMul,
      ZornParavectorNullspace.cross3, huX1, huX2, hvX1, hvX2,
      huY1, huY2, hvY1, hvY2]
  constructor
  · simp [ZornParavectorNullspace.zornMul,
      ZornParavectorNullspace.cross3, huX1, huX2, hvX1, hvX2,
      huY1, huY2, hvY1, hvY2]
  constructor
  · simp [ZornParavectorNullspace.zornMul,
      ZornParavectorNullspace.cross3, huX1, huX2, hvX1, hvX2,
      huY1, huY2, hvY1, hvY2]
  · simp [ZornParavectorNullspace.zornMul,
      ZornParavectorNullspace.cross3, huX1, huX2, hvX1, hvX2,
      huY1, huY2, hvY1, hvY2]

theorem bridgeCarrierMap_restricted_mul
    {X Y : RestrictedZorn} :
    bridgeCarrierMap (ZornParavectorNullspace.zornMul X.1 Y.1) =
      bridgeCarrierMap X.1 * bridgeCarrierMap Y.1 := by
  rcases X with ⟨X, hX⟩
  rcases Y with ⟨Y, hY⟩
  rcases hX with ⟨huX1, huX2, hvX1, hvX2⟩
  rcases hY with ⟨huY1, huY2, hvY1, hvY2⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bridgeCarrierMap, ZornParavectorNullspace.zornMul,
      ZornParavectorNullspace.dot3, ZornParavectorNullspace.cross3,
      Fin.sum_univ_three,
      huX1, huX2, hvX1, hvX2, huY1, huY2, hvY1, hvY2] <;>
    ring

/-- Canonical upper nilpotent lane used by the local bridge. -/
def bridgeCanonicalUpper : ZornParavectorNullspace.Zorn :=
  { a := 0, b := 0, u := fun | 0 => 1 | _ => 0, v := fun _ => 0 }

/-- Canonical lower nilpotent lane used by the local bridge. -/
def bridgeCanonicalLower : ZornParavectorNullspace.Zorn :=
  ZornParavectorNullspace.collapsedLower (fun | 0 => 1 | _ => 0)

/-- The source-defined bracket compatibility on the canonical upper/lower
lanes: commutator, anticommutator, and square-zero relations all match the
chiral CAR spine. -/
theorem bridgeCarrier_upper_unit_is_sigmaPlus :
    bridgeCarrierMap bridgeCanonicalUpper = ChiralCausalCone.σPlus := by
  simp [bridgeCarrierMap, bridgeCanonicalUpper, ChiralCausalCone.σPlus]

theorem bridgeCarrier_lower_unit_is_sigmaMinus :
    bridgeCarrierMap bridgeCanonicalLower = ChiralCausalCone.σMinus := by
  simp [bridgeCarrierMap, bridgeCanonicalLower, ZornParavectorNullspace.collapsedLower,
    ChiralCausalCone.σMinus]

theorem bridgeCarrier_collapsed_maps_to_lower (p : ZornParavectorNullspace.Vec3) :
    bridgeCarrierMap (ZornParavectorNullspace.collapsedLower p) = !![0, 0; p 0, 0] := by
  simp [bridgeCarrierMap, ZornParavectorNullspace.collapsedLower]

theorem bridgeCarrier_image_nilpotent (p : ZornParavectorNullspace.Vec3) :
    bridgeCarrierMap (ZornParavectorNullspace.collapsedLower p) *
      bridgeCarrierMap (ZornParavectorNullspace.collapsedLower p) = 0 := by
  rw [bridgeCarrier_collapsed_maps_to_lower]
  ext i j
  fin_cases i
  · fin_cases j
    · simp
    · simp
  · fin_cases j
    · simp
    · simp

theorem bridgeCarrier_bracket_compatibility :
    bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalLower -
      bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalUpper =
        ChiralCausalCone.σ3c ∧
    bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalLower +
      bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalUpper =
        (1 : ChiralCausalCone.M2C) ∧
    bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalUpper = 0 ∧
    bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalLower = 0 := by
  have hUpperLower_comm :
      bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalLower -
        bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalUpper =
          ChiralCausalCone.σ3c := by
    rw [bridgeCarrier_upper_unit_is_sigmaPlus, bridgeCarrier_lower_unit_is_sigmaMinus]
    exact ChiralCausalCone.comm_σPlus_σMinus
  have hUpperLower_anti :
      bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalLower +
        bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalUpper =
          (1 : ChiralCausalCone.M2C) := by
    rw [bridgeCarrier_upper_unit_is_sigmaPlus, bridgeCarrier_lower_unit_is_sigmaMinus]
    exact ChiralCausalCone.anti_σPlus_σMinus
  have hUpper_sq :
      bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalUpper = 0 := by
    rw [bridgeCarrier_upper_unit_is_sigmaPlus]
    exact ChiralCausalCone.σPlus_sq
  have hLower_sq :
      bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalLower = 0 := by
    rw [bridgeCarrier_lower_unit_is_sigmaMinus]
    exact ChiralCausalCone.σMinus_sq
  exact ⟨hUpperLower_comm, hUpperLower_anti, hUpper_sq, hLower_sq⟩

/-- The outer `2×2` carrier for the spinor pair: it stores two inner Zorn
slots and lets the modular glide act only by swapping those slots. -/
abbrev OuterSpinorCarrier :=
  ZornParavectorNullspace.Zorn × ZornParavectorNullspace.Zorn

/-- The outer modular glide on the pair carrier. -/
def outerMirror : OuterSpinorCarrier → OuterSpinorCarrier := Prod.swap

@[simp] theorem outerMirror_involutive (x : OuterSpinorCarrier) :
    outerMirror (outerMirror x) = x := by
  cases x with
  | mk a b => rfl

/-- The carrier map applied componentwise to the outer pair. -/
def outerCarrierMap : OuterSpinorCarrier →
    ChiralCausalCone.M2C × ChiralCausalCone.M2C :=
  Prod.map bridgeCarrierMap bridgeCarrierMap

/-- The outer glide commutes with the componentwise carrier map. -/
theorem outerCarrierMap_mirror_commutes (x : OuterSpinorCarrier) :
    outerCarrierMap (outerMirror x) = Prod.swap (outerCarrierMap x) := by
  cases x with
  | mk a b => rfl

/-- The outer nested carrier also preserves the inner bracket compatibility
when the canonical upper/lower lanes are selected in the two slots. -/
theorem outerCarrierMap_bracket_compatibility :
    outerCarrierMap (bridgeCanonicalUpper, bridgeCanonicalLower) =
      (bridgeCarrierMap bridgeCanonicalUpper, bridgeCarrierMap bridgeCanonicalLower) ∧
    outerCarrierMap (outerMirror (bridgeCanonicalUpper, bridgeCanonicalLower)) =
      (bridgeCarrierMap bridgeCanonicalLower, bridgeCarrierMap bridgeCanonicalUpper) ∧
    bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalLower -
      bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalUpper =
        ChiralCausalCone.σ3c := by
  have hFirst :
      outerCarrierMap (bridgeCanonicalUpper, bridgeCanonicalLower) =
        (bridgeCarrierMap bridgeCanonicalUpper, bridgeCarrierMap bridgeCanonicalLower) := by
    rfl
  have hSecond :
      outerCarrierMap (outerMirror (bridgeCanonicalUpper, bridgeCanonicalLower)) =
        (bridgeCarrierMap bridgeCanonicalLower, bridgeCarrierMap bridgeCanonicalUpper) := by
    rfl
  have hBracket :
      bridgeCarrierMap bridgeCanonicalUpper * bridgeCarrierMap bridgeCanonicalLower -
        bridgeCarrierMap bridgeCanonicalLower * bridgeCarrierMap bridgeCanonicalUpper =
          ChiralCausalCone.σ3c := by
    exact (bridgeCarrier_bracket_compatibility).1
  exact ⟨hFirst, hSecond, hBracket⟩

/-- The carrier summary tying the `Pin(5,5)` scaffold to the chiral/Zorn/TKK spine. -/
structure BridgeSummary where
  pin55_lower_generator :
    Clifford55.ι55 (Clifford55.f_neg PinO55GlideReflection.crosscapIndex) ∈ Clifford55.Pin55
  pin55_central_sign : (-1 : Clifford55.Cl55) ∈ Clifford55.Pin55
  pin55_split_index_zero : anomalyIndex 5 5 = 0
  chiral_projector_sum :
    ChiralCausalConeTKKBridge.SPlus + ChiralCausalConeTKKBridge.SMinus = (1 : ChiralCausalCone.M2C)
  chiral_nilpotent_source :
    ChiralCausalConeTKKBridge.NPlus * ChiralCausalConeTKKBridge.NPlus = 0 ∧
    ChiralCausalConeTKKBridge.NMinus * ChiralCausalConeTKKBridge.NMinus = 0
  zorn_weld :
    (bridgeCarrierMap bridgeCanonicalLower = ChiralCausalCone.σMinus) ∧
    (bridgeCarrierMap bridgeCanonicalUpper =
      ChiralCausalCone.σPlus) ∧
    (∀ p : ZornParavectorNullspace.Vec3,
      bridgeCarrierMap (ZornParavectorNullspace.collapsedLower p) *
        bridgeCarrierMap (ZornParavectorNullspace.collapsedLower p) = 0)
  zorn_bracket_compatibility :
    bridgeCarrierMap bridgeCanonicalUpper *
      bridgeCarrierMap bridgeCanonicalLower -
      bridgeCarrierMap bridgeCanonicalLower *
      bridgeCarrierMap bridgeCanonicalUpper =
        ChiralCausalCone.σ3c ∧
    bridgeCarrierMap bridgeCanonicalUpper *
      bridgeCarrierMap bridgeCanonicalLower +
      bridgeCarrierMap bridgeCanonicalLower *
      bridgeCarrierMap bridgeCanonicalUpper = (1 : ChiralCausalCone.M2C) ∧
    bridgeCarrierMap bridgeCanonicalUpper *
      bridgeCarrierMap bridgeCanonicalUpper = 0 ∧
      bridgeCarrierMap bridgeCanonicalLower *
      bridgeCarrierMap bridgeCanonicalLower = 0
  outer_pair_commutes :
    outerCarrierMap (outerMirror (bridgeCanonicalUpper, bridgeCanonicalLower)) =
      Prod.swap (outerCarrierMap (bridgeCanonicalUpper, bridgeCanonicalLower))
  tkk_lane_grade :
    ZornTrialityTKKBridge.laneGrade ZornTrialityTKKBridge.SplitOctonionLane.diagonalProjector =
      TKKJordanPairData.TKKGrade.z0 ∧
    ZornTrialityTKKBridge.laneGrade ZornTrialityTKKBridge.SplitOctonionLane.upperNilpotent =
      TKKJordanPairData.TKKGrade.p1 ∧
    ZornTrialityTKKBridge.laneGrade ZornTrialityTKKBridge.SplitOctonionLane.lowerNilpotent =
      TKKJordanPairData.TKKGrade.m1 ∧
    ZornTrialityTKKBridge.laneGrade ZornTrialityTKKBridge.SplitOctonionLane.associatorWitness =
      TKKJordanPairData.TKKGrade.p2 ∧
    ZornTrialityTKKBridge.laneMirror
        (ZornTrialityTKKBridge.laneMirror
          ZornTrialityTKKBridge.SplitOctonionLane.upperNilpotent) =
      ZornTrialityTKKBridge.SplitOctonionLane.upperNilpotent

/-- The actual bridge theorem: `Pin(5,5)` carrier facts, chiral projectors,
Zorn weld, and TKK grading sit in one finite package. -/
def pin55_chiral_zorn_tkk_synthesis : BridgeSummary := by
  refine
    { pin55_lower_generator := PinO55GlideReflection.f_neg_mem_pin55 PinO55GlideReflection.crosscapIndex
      pin55_central_sign := ArtinCentralizerMonodromy.neg_one_mem_pin55
      pin55_split_index_zero := Pin55CartanDecomposition.split_signature_index_55_zero
      chiral_projector_sum := ChiralCausalConeTKKBridge.projector_sum
      chiral_nilpotent_source := ChiralCausalConeTKKBridge.nilpotent_source
      zorn_weld := ⟨bridgeCarrier_lower_unit_is_sigmaMinus,
        bridgeCarrier_upper_unit_is_sigmaPlus, bridgeCarrier_image_nilpotent⟩
      zorn_bracket_compatibility := bridgeCarrier_bracket_compatibility
      outer_pair_commutes := outerCarrierMap_mirror_commutes
        (bridgeCanonicalUpper, bridgeCanonicalLower)
      tkk_lane_grade := ZornTrialityTKKBridge.canonical_lane_grade_synthesis }

end Pin55ChiralZornTKKBridge

end
