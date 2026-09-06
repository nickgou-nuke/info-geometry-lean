import InfoGeometry.Lie.SplitOctonionCartanSixWeights
import InfoGeometry.Canonical.HexIndexSplitOctonionBridge
import InfoGeometry.Canonical.D6SixModeAction

/-!
# Dihedral hexagon of the six circular Cartan weights

This owner transports the six concrete signed Cartan weights to the native
hexagonal labels and records the order-six rotation/reflection relations.
Here `DihedralGroup 6` means the order-twelve symmetry group `I₂(6)` of a
hexagon.  It is unrelated to the Dynkin type `D₆`, and this file does not
assert the twelve-root adjoint decomposition of `G₂`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Canonical.D6SixModeAction
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionCartanSixWeights
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-- The actual canonical Zorn circular vector at a hexagonal label. -/
def circularChannel (n : HexIndex) : ZornMatrix ℝ :=
  let p := sheetColorEquiv n
  if hexSheetFin2 p.1 = 0 then
    cartesianZornLinearEquiv (rootPlus p.2)
  else
    cartesianZornLinearEquiv (rootMinus p.2)

@[simp] theorem circularChannel_positive (i : HexColor) :
    circularChannel (positiveVertex i) =
      cartesianZornLinearEquiv (rootPlus i) := by
  fin_cases i <;> rfl

@[simp] theorem circularChannel_negative (i : HexColor) :
    circularChannel (negativeVertex i) =
      cartesianZornLinearEquiv (rootMinus i) := by
  fin_cases i <;> rfl

def circularChannelFrameIndex : HexIndex → Fin 8
  | 0 => 1
  | 1 => 7
  | 2 => 2
  | 3 => 5
  | 4 => 3
  | 5 => 6

@[simp] theorem circularChannel_eq_circularFrame (n : HexIndex) :
    circularChannel n =
      cartesianZornLinearEquiv (circularFrame (circularChannelFrameIndex n)) := by
  fin_cases n <;> rfl

theorem circularChannelFrameIndex_injective :
    Function.Injective circularChannelFrameIndex := by
  intro m n h
  fin_cases m <;> fin_cases n <;> simp [circularChannelFrameIndex] at h ⊢

theorem circularChannel_injective :
    Function.Injective circularChannel := by
  intro m n h
  have hframe :
      circularFrame (circularChannelFrameIndex m) =
        circularFrame (circularChannelFrameIndex n) := by
    apply cartesianZornLinearEquiv.injective
    simpa only [circularChannel_eq_circularFrame] using h
  have hcoordinates := congrArg circularCoordinate hframe
  have hindex : circularChannelFrameIndex m = circularChannelFrameIndex n := by
    by_contra hne
    have he := congrFun hcoordinates (circularChannelFrameIndex m)
    simp [circularCoordinate_frame, hne, Ne.symm hne] at he
  exact circularChannelFrameIndex_injective hindex

theorem circularChannel_sheetReflection (n : HexIndex) :
    circularChannel (sheetReflection n) =
      if (sheetColorEquiv n).1 = .positive then
        circularChannel (negativeVertex ⟨(3 - (sheetColorEquiv n).2).val % 3, by omega⟩)
      else
        circularChannel (positiveVertex ⟨(3 - (sheetColorEquiv n).2).val % 3, by omega⟩) := by
  fin_cases n <;> simp [sheetReflection, sheetColorEquiv, sheetOf, colorOf,
    hexSheetFin2, circularChannel, positiveVertex, negativeVertex]

theorem circularChannel_colorRotation (n : HexIndex) :
    circularChannel (colorRotation n) =
      circularChannel (match (sheetColorEquiv n).1 with
        | .positive => positiveVertex ⟨((sheetColorEquiv n).2.val + 1) % 3, by omega⟩
        | .negative => negativeVertex ⟨((sheetColorEquiv n).2.val + 1) % 3, by omega⟩) := by
  fin_cases n <;> simp [colorRotation, sheetColorEquiv, sheetOf, colorOf,
    hexSheetFin2, circularChannel, positiveVertex, negativeVertex]

/-! The rotation of the hexagon is already a concrete cyclic reindexing of the
actual upper and lower Zorn channels.  These readouts deliberately stop at
the carrier level: they do not assert that the reindexing preserves the Zorn
multiplication table. -/

theorem circularChannel_colorRotation_positive (i : HexColor) :
    circularChannel (colorRotation (positiveVertex i)) =
      circularChannel (positiveVertex ⟨(i.val + 1) % 3, by omega⟩) := by
  rw [colorRotation_positive]

theorem circularChannel_colorRotation_negative (i : HexColor) :
    circularChannel (colorRotation (negativeVertex i)) =
      circularChannel (negativeVertex ⟨(i.val + 1) % 3, by omega⟩) := by
  rw [colorRotation_negative]

/-- The six actual circular Zorn vectors in cyclic `ZMod 6` order. -/
def cyclotomicChannel (n : D6Index) : ZornMatrix ℝ :=
  circularChannel (zmodIndex.symm n)

@[simp] theorem cyclotomicChannel_zero :
    cyclotomicChannel 0 = cartesianZornLinearEquiv (rootPlus 0) := rfl

@[simp] theorem cyclotomicChannel_one :
    cyclotomicChannel 1 = cartesianZornLinearEquiv (rootMinus 2) := rfl

@[simp] theorem cyclotomicChannel_two :
    cyclotomicChannel 2 = cartesianZornLinearEquiv (rootPlus 1) := rfl

@[simp] theorem cyclotomicChannel_three :
    cyclotomicChannel 3 = cartesianZornLinearEquiv (rootMinus 0) := rfl

@[simp] theorem cyclotomicChannel_four :
    cyclotomicChannel 4 = cartesianZornLinearEquiv (rootPlus 2) := rfl

@[simp] theorem cyclotomicChannel_five :
    cyclotomicChannel 5 = cartesianZornLinearEquiv (rootMinus 1) := rfl

/-! The order-six label rotation has a native order-three colour square on the
actual circular carrier.  This is a carrier-level identity only; it does not
promote the unsigned order-six action to a multiplication automorphism. -/

theorem cyclotomicChannel_rotation_two (n : D6Index) :
    cyclotomicChannel (rotation 2 n) =
      circularChannel (colorRotation (zmodIndex.symm n)) := by
  fin_cases n <;> rfl

theorem cyclotomicChannel_reflection_shifted (n : D6Index) :
    circularChannel (sheetReflection (zmodIndex.symm n)) =
      cyclotomicChannel (reflection n + 3) := by
  fin_cases n <;> rfl

/-- The six signed Cartan weights, ordered around the native hexagon. -/
def hexWeight (n : HexIndex) : TracelessWeight →ₗ[ℝ] ℝ :=
  let p := sheetColorEquiv n
  signedWeight (hexSheetFin2 p.1, p.2)

@[simp] theorem hexWeight_positive (i : HexColor) :
    hexWeight (positiveVertex i) = weightFunctional i := by
  fin_cases i <;> rfl

@[simp] theorem hexWeight_negative (i : HexColor) :
    hexWeight (negativeVertex i) = -weightFunctional i := by
  fin_cases i <;> rfl

/-- The same hexagonal spectrum on the additive cyclic label `ZMod 6`. -/
def cyclotomicWeight (n : D6Index) : TracelessWeight →ₗ[ℝ] ℝ :=
  hexWeight (zmodIndex.symm n)

/-- Rotation reindexes the concrete six-weight spectrum. -/
def rotateWeights (k : D6Index) :
    D6Index → (TracelessWeight →ₗ[ℝ] ℝ) :=
  modeRotate k cyclotomicWeight

/-- Reflection reindexes the concrete six-weight spectrum. -/
def reflectWeights : D6Index → (TracelessWeight →ₗ[ℝ] ℝ) :=
  modeReflect cyclotomicWeight

/-- Rotation reindexes the six actual circular Zorn vectors. -/
def rotateChannels (k : D6Index) : D6Index → ZornMatrix ℝ :=
  modeRotate k cyclotomicChannel

/-- Reflection reindexes the six actual circular Zorn vectors. -/
def reflectChannels : D6Index → ZornMatrix ℝ :=
  modeReflect cyclotomicChannel

@[simp] theorem rotateChannels_apply (k n : D6Index) :
    rotateChannels k n = cyclotomicChannel (rotation k n) := rfl

@[simp] theorem reflectChannels_apply (n : D6Index) :
    reflectChannels n = cyclotomicChannel (reflection n) := rfl

theorem rotateWeights_add (k l : D6Index) :
    modeRotate (k + l) cyclotomicWeight =
      modeRotate l (modeRotate k cyclotomicWeight) :=
  modeRotate_add k l cyclotomicWeight

theorem reflectWeights_involutive :
    modeReflect (modeReflect cyclotomicWeight) = cyclotomicWeight :=
  modeReflect_involutive cyclotomicWeight

theorem reflect_rotate_reflect (k : D6Index) :
    modeReflect (modeRotate k (modeReflect cyclotomicWeight)) =
      modeRotate (-k) cyclotomicWeight :=
  modeReflect_rotate_reflect k cyclotomicWeight

theorem rotateChannels_add (k l : D6Index) :
    modeRotate (k + l) cyclotomicChannel =
      modeRotate l (modeRotate k cyclotomicChannel) :=
  modeRotate_add k l cyclotomicChannel

theorem reflectChannels_involutive :
    modeReflect (modeReflect cyclotomicChannel) = cyclotomicChannel :=
  modeReflect_involutive cyclotomicChannel

theorem reflect_rotate_channels_reflect (k : D6Index) :
    modeReflect (modeRotate k (modeReflect cyclotomicChannel)) =
      modeRotate (-k) cyclotomicChannel :=
  modeReflect_rotate_reflect k cyclotomicChannel

/-- The acting Weyl/dihedral group has twelve elements. -/
theorem dihedralGroupSix_card : Fintype.card (DihedralGroup 6) = 12 := by
  simp [DihedralGroup.card]

end InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon
