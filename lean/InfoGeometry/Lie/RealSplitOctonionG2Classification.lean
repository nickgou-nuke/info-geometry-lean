import Mathlib.Data.Nat.Basic

/-!
# Real split `G_{2(2)}` from exact computer algebra

This file records only the exact computer-algebra certificate for the
split-octonion derivation algebra. It introduces no replacement real Lie-group
object and it does not conflate the finite Chevalley group `G₂(2)` with the
real split form `G_{2(2)}`.

The executable certificate is produced by
`tools/infra/real_split_g2_classification/real_split_g2_exact_ca.py` from the
primitive Zorn product over `QQ`.
-/

namespace InfoGeometry.Lie.RealSplitOctonionG2Classification

/-- Status of the real split-octonion classification lane. -/
inductive RealClassificationStatus where
  | exactComputerAlgebraLieAlgebra
  | nativeLeanGroupEquivalence
  deriving DecidableEq, Repr

/-- Exact certificate values recomputed by the computer-algebra lane. -/
structure ExactComputerAlgebraPacket where
  /-- Derivation constraint rows: 8 products × 8 output coordinates. -/
  derivationRows : ℕ
  /-- Unknowns in an 8×8 endomorphism matrix. -/
  derivationCols : ℕ
  /-- Rank of the derivation constraint matrix over `QQ`. -/
  derivationRank : ℕ
  /-- Nullity of the derivation constraint matrix over `QQ`. -/
  derivationNullity : ℕ
  /-- Number of exact nullspace basis derivations. -/
  basisCount : ℕ
  /-- Rank of the Killing form computed from exact adjoint matrices. -/
  killingRank : ℕ
  /-- Positive inertia count of the exact Killing form. -/
  killingPositive : ℕ
  /-- Negative inertia count of the exact Killing form. -/
  killingNegative : ℕ
  /-- Zero inertia count of the exact Killing form. -/
  killingZero : ℕ
  /-- Whether all commutators were solved exactly in the computed basis. -/
  bracketClosed : Bool
  /-- Maximum denominator in the computed structure constants. -/
  structureConstantsMaxDenominator : ℕ
  /-- Sage/GAP root-system ledger: `G₂` has 12 roots. -/
  rootCount : ℕ
  /-- Sage root-system ledger: `G₂` has 6 positive roots. -/
  positiveRootCount : ℕ
  /-- GAP/Sage Weyl-group ledger: `|W(G₂)| = 12`. -/
  weylOrder : ℕ
  /-- Finite Chevalley/Atlas `G₂(2)` order, kept as a separate boundary value. -/
  finiteG2TwoOrder : ℕ

/-- The exact computer-algebra packet for the Zorn split-octonion derivation algebra. -/
def realSplitOctonionLiePacket : ExactComputerAlgebraPacket where
  derivationRows := 512
  derivationCols := 64
  derivationRank := 50
  derivationNullity := 14
  basisCount := 14
  killingRank := 14
  killingPositive := 8
  killingNegative := 6
  killingZero := 0
  bracketClosed := true
  structureConstantsMaxDenominator := 1
  rootCount := 12
  positiveRootCount := 6
  weylOrder := 12
  finiteG2TwoOrder := 12096

/-- The current closed status is exact computer algebra for the Lie algebra, not a native group equivalence. -/
def currentRealClassificationStatus : RealClassificationStatus :=
  RealClassificationStatus.exactComputerAlgebraLieAlgebra

/-- Read back all exact CA values used by the wrapper. -/
theorem realSplitOctonionLiePacket_packet :
    realSplitOctonionLiePacket.derivationRows = 512 ∧
      realSplitOctonionLiePacket.derivationCols = 64 ∧
      realSplitOctonionLiePacket.derivationRank = 50 ∧
      realSplitOctonionLiePacket.derivationNullity = 14 ∧
      realSplitOctonionLiePacket.basisCount = 14 ∧
      realSplitOctonionLiePacket.killingRank = 14 ∧
      realSplitOctonionLiePacket.killingPositive = 8 ∧
      realSplitOctonionLiePacket.killingNegative = 6 ∧
      realSplitOctonionLiePacket.killingZero = 0 ∧
      realSplitOctonionLiePacket.bracketClosed = true ∧
      realSplitOctonionLiePacket.structureConstantsMaxDenominator = 1 ∧
      realSplitOctonionLiePacket.rootCount = 12 ∧
      realSplitOctonionLiePacket.positiveRootCount = 6 ∧
      realSplitOctonionLiePacket.weylOrder = 12 ∧
      realSplitOctonionLiePacket.finiteG2TwoOrder = 12096 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Rank-nullity readback: the exact derivation algebra has dimension `14`. -/
theorem derivation_rank_nullity :
    realSplitOctonionLiePacket.derivationRank +
        realSplitOctonionLiePacket.derivationNullity =
      realSplitOctonionLiePacket.derivationCols := by
  rfl

/-- The exact Killing-form inertia is split: `(8,6,0)` up to global sign convention. -/
theorem killing_inertia_split :
    realSplitOctonionLiePacket.killingPositive = 8 ∧
      realSplitOctonionLiePacket.killingNegative = 6 ∧
      realSplitOctonionLiePacket.killingZero = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Finite `G₂(2)` remains a separate finite-order boundary value. -/
theorem finite_g2two_boundary_order :
    realSplitOctonionLiePacket.finiteG2TwoOrder = 12096 := by
  rfl

/-- The exact CA packet is not a native Lean group-equivalence theorem. -/
theorem current_status_is_not_native_group_equivalence :
    currentRealClassificationStatus ≠ RealClassificationStatus.nativeLeanGroupEquivalence := by
  decide

end InfoGeometry.Lie.RealSplitOctonionG2Classification
