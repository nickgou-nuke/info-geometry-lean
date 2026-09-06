import InfoGeometry.Canonical.C12CyclotomicPhase
import InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction

/-!
# The split-octonion C12-to-hexagon carrier bridge

The twelve-fold cyclic phase and the six-channel Zorn hexagon are distinct
carriers.  This owner records their canonical quotient and the fact that the
native multiplicative Zorn cycle is the step-two, rather than step-one,
rotation on the six-channel quotient.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionC12HexagonBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.C12CyclotomicPhase
open InfoGeometry.Canonical.D6SixModeAction
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon
open InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction

/-- The six-channel Zorn readout of a twelve-fold phase label. -/
def c12Channel (k : C12Index) : ZornMatrix ℝ :=
  cyclotomicChannel (toSixMode k)

@[simp] theorem c12Channel_halfTurn (k : C12Index) :
    c12Channel (k + 6) = c12Channel k := by
  unfold c12Channel
  rw [toSixMode_halfTurn_add]

@[simp] theorem c12Channel_zero :
    c12Channel 0 = cyclotomicChannel 0 := by
  simp [c12Channel]

@[simp] theorem c12Channel_six :
    c12Channel 6 = c12Channel 0 := by
  simpa using c12Channel_halfTurn (0 : C12Index)

/-! The surviving multiplicative Zorn cycle is the order-three subgroup of the
six-channel quotient, hence the order-six phase advances by two labels. -/

theorem canonicalColorCycle_c12Channel (k : C12Index) :
    canonicalColorCycle (c12Channel k) = c12Channel (k + 2) := by
  unfold c12Channel
  rw [canonicalColorCycle_cyclotomicChannel]
  rw [toSixMode_add]
  rfl

theorem canonicalColorReflection_c12Channel (k : C12Index) :
    canonicalColorReflection (c12Channel k) =
      cyclotomicChannel (reflection (toSixMode k) + 3) := by
  exact canonicalColorReflection_cyclotomicChannel (toSixMode k)

end InfoGeometry.Lie.SplitOctonionC12HexagonBridge
