import InfoGeometry.Canonical.ZornSpinor
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.RealSplitOctonionG2Classification

/-!
# Real split-octonion derivation witness

This file provides the native computer-algebra derivation witness on the real
canonical Zorn carrier. It does not claim the final automorphism-group
classification.
-/

noncomputable section

namespace InfoGeometry.Lie.RealSplitOctonionDerivationWitness

open RealSplitOctonionG2Classification

open scoped BigOperators

/-- The canonical real split-octonion carrier. -/
abbrev SplitOctReal := InfoGeometry.Canonical.ZornMatrix ℝ

/-- Infinitesimal rotation in the `0-1` plane, on both vector slots. -/
def rot01Real (z : SplitOctReal) : SplitOctReal :=
  { a := 0,
    b := 0,
    x := ![z.x 1, -z.x 0, 0],
    y := ![z.y 1, -z.y 0, 0] }

/-- Addition law for the real `0-1` rotation derivation. -/
theorem rot01Real_add : ∀ X Y : SplitOctReal, rot01Real (X + Y) = rot01Real X + rot01Real Y := by
  intro X Y
  cases X
  cases Y
  ext
  · simp [rot01Real]
  · simp [rot01Real]
  · rename_i i
    fin_cases i <;> simp [rot01Real] <;> ring_nf
  · rename_i i
    fin_cases i <;> simp [rot01Real] <;> ring_nf

/-- Negation law for the real `0-1` rotation derivation. -/
theorem rot01Real_neg : ∀ X : SplitOctReal, rot01Real (-X) = - rot01Real X := by
  intro X
  cases X
  ext
  · simp [rot01Real]
  · simp [rot01Real]
  · rename_i i
    fin_cases i <;> simp [rot01Real] <;> ring_nf
  · rename_i i
    fin_cases i <;> simp [rot01Real] <;> ring_nf

/-- Leibniz law for the real `0-1` rotation derivation. -/
theorem rot01Real_mul : ∀ X Y : SplitOctReal, rot01Real (X * Y) = rot01Real X * Y + X * rot01Real Y := by
  intro X Y
  cases X
  cases Y
  ext
  · simp [rot01Real, InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;> ring_nf
  · simp [rot01Real, InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;> ring_nf
  · rename_i i
    fin_cases i <;>
      simp [rot01Real, InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail] <;> ring_nf
  · rename_i i
    fin_cases i <;>
      simp [rot01Real, InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail] <;> ring_nf

/-- The real `0-1` rotation is a derivation. -/
theorem rot01Real_deriv :
    (∀ X Y : SplitOctReal, rot01Real (X + Y) = rot01Real X + rot01Real Y) ∧
      (∀ X : SplitOctReal, rot01Real (-X) = - rot01Real X) ∧
        ∀ X Y : SplitOctReal, rot01Real (X * Y) = rot01Real X * Y + X * rot01Real Y := by
  exact ⟨rot01Real_add, rot01Real_neg, rot01Real_mul⟩

/-- Native derivation witness packet on the real split-octonion carrier. -/
structure RealSplitOctonionDerivationPacket where
  status : RealClassificationStatus
  derivation : (∀ X Y : SplitOctReal, rot01Real (X + Y) = rot01Real X + rot01Real Y) ∧
    (∀ X : SplitOctReal, rot01Real (-X) = - rot01Real X) ∧
      ∀ X Y : SplitOctReal, rot01Real (X * Y) = rot01Real X * Y + X * rot01Real Y

/-- The canonical native packet for the real derivation witness. -/
def realSplitOctonionDerivationPacket : RealSplitOctonionDerivationPacket where
  status := currentRealClassificationStatus
  derivation := rot01Real_deriv

/-- Readback for the native derivation witness packet. -/
theorem realSplitOctonionDerivationPacket_packet :
    realSplitOctonionDerivationPacket.status =
      currentRealClassificationStatus ∧
      realSplitOctonionDerivationPacket.derivation = rot01Real_deriv := by
  exact ⟨rfl, rfl⟩

/-- A concrete `up0` input for the real rotation witness. -/
abbrev up0 : SplitOctReal := { a := 0, b := 0, x := ![1, 0, 0], y := 0 }

/-- Coordinate readout: the real `0-1` rotation on `up0`. -/
theorem rot01Real_up0_readout :
    (rot01Real up0).a = 0 ∧
      (rot01Real up0).b = 0 ∧
      (rot01Real up0).x 0 = 0 ∧
      (rot01Real up0).x 1 = -1 ∧
      (rot01Real up0).x 2 = 0 ∧
      (rot01Real up0).y 0 = 0 ∧
      (rot01Real up0).y 1 = 0 ∧
      (rot01Real up0).y 2 = 0 := by
  simp [rot01Real, up0]

/-- The real `0-1` rotation is nonzero on `up0`. -/
theorem rot01Real_nonzero_on_up0 : rot01Real up0 ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : SplitOctReal => z.x 1) h
  change -1 = 0 at h1
  norm_num at h1

end InfoGeometry.Lie.RealSplitOctonionDerivationWitness
