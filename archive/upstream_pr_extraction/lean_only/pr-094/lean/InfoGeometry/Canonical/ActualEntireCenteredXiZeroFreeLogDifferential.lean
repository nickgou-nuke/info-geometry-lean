import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential
import InfoGeometry.Canonical.ActualEntireCenteredXiLogDerivativeBridge

/-!
# The centered zero-free domain for the actual completed xi readout

This owner transports the actual zero-free logarithmic readout through the
affine coordinate `s = 1 / 2 + z`.  The centered reflection is therefore a
typed map on the actual domain.  No global zero enumeration, period, or
cohomology statement is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireCenteredXiZeroFreeLogDifferential

open Complex
open InfoGeometry.Canonical.ActualEntireCenteredXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential

abbrev ActualCenteredXiZeroFreePoint :=
  {z : ℂ // z ∈ actualEntireCenteredXiZeroFreeLocus}

def centeredToEntireXiZeroFree
    (z : ActualCenteredXiZeroFreePoint) : EntireXiZeroFreePoint :=
  ⟨(1 / 2 : ℂ) + z.1, z.property⟩

def centeredReflectZeroFree
    (z : ActualCenteredXiZeroFreePoint) : ActualCenteredXiZeroFreePoint :=
  ⟨-z.1, (actualEntireCenteredXiZeroFree_neg_iff z.1).2 z.property⟩

def actualCenteredXiLogOneFormOnZeroFree
    (z : ActualCenteredXiZeroFreePoint) : ℂ →L[ℂ] ℂ :=
  entireRiemannXiLogOneFormOnZeroFree (centeredToEntireXiZeroFree z)

@[simp] theorem centeredToEntireXiZeroFree_coe
    (z : ActualCenteredXiZeroFreePoint) :
    (centeredToEntireXiZeroFree z).1 = (1 / 2 : ℂ) + z.1 := rfl

theorem actualCenteredXiLogOneFormOnZeroFree_eq
    (z : ActualCenteredXiZeroFreePoint) :
    actualCenteredXiLogOneFormOnZeroFree z =
      actualEntireCenteredXiLogOneForm z.1 := by
  rfl

theorem actualCenteredXiLogOneFormOnZeroFree_reflection_pullback
    (z : ActualCenteredXiZeroFreePoint) (v : ℂ) :
    actualCenteredXiLogOneFormOnZeroFree (centeredReflectZeroFree z) (-v) =
      actualCenteredXiLogOneFormOnZeroFree z v := by
  change
    entireRiemannXiLogOneForm ((1 / 2 : ℂ) + (-z.1)) (-v) =
      entireRiemannXiLogOneForm ((1 / 2 : ℂ) + z.1) v
  have hcoord :
      (1 / 2 : ℂ) + (-z.1) = 1 - ((1 / 2 : ℂ) + z.1) := by
    ring
  rw [hcoord]
  exact entireRiemannXiLogOneForm_reflection_pullback _ v

end InfoGeometry.Canonical.ActualEntireCenteredXiZeroFreeLogDifferential
