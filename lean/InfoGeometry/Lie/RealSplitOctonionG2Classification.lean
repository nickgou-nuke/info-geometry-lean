import Mathlib.Data.Nat.Basic

/-!
# Real split `G_{2(2)}` from exact computer algebra

This file records the exact computer-algebra certificate for the
split-octonion derivation algebra. It keeps the finite Chevalley group `G₂(2)`
and the real split form `G_{2(2)}` in separate lanes.

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
  /-- Exact CA checked the canonical Zorn unit is two-sided on the basis. -/
  zornUnitTwoSided : Bool
  /-- Positive inertia of the split-octonion norm form. -/
  normPositive : ℕ
  /-- Negative inertia of the split-octonion norm form. -/
  normNegative : ℕ
  /-- Zero inertia of the split-octonion norm form. -/
  normZero : ℕ
  /-- Exact symbolic CA checked `N(XY)=N(X)N(Y)`. -/
  normMultiplicativeSymbolic : Bool
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
  /-- Macaulay2 `Dmodules` lane checked the Weyl commutators on the rank-two chart. -/
  dmodulesWeylCommutators : Bool
  /-- Macaulay2 `Dmodules` lane checked the six positive-root chart. -/
  dmodulesRootChart : Bool
  /-- Degree of the product of the six positive `G₂` root forms in the D-module chart. -/
  dmodulesRootArrangementDegree : ℕ
  /-- Macaulay2 `Dmodules` lane checked holonomicity of the Cartan chart module. -/
  dmodulesHolonomic : Bool

/-- The exact computer-algebra packet for the Zorn split-octonion derivation algebra. -/
def realSplitOctonionLiePacket : ExactComputerAlgebraPacket where
  zornUnitTwoSided := true
  normPositive := 4
  normNegative := 4
  normZero := 0
  normMultiplicativeSymbolic := true
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
  dmodulesWeylCommutators := true
  dmodulesRootChart := true
  dmodulesRootArrangementDegree := 6
  dmodulesHolonomic := true

/-! The current closed status records exact computer algebra for the Lie algebra. -/
def currentRealClassificationStatus : RealClassificationStatus :=
  RealClassificationStatus.exactComputerAlgebraLieAlgebra

/-- Read back all exact CA values used by the wrapper. -/
theorem realSplitOctonionLiePacket_packet :
    realSplitOctonionLiePacket.zornUnitTwoSided = true ∧
      realSplitOctonionLiePacket.normPositive = 4 ∧
      realSplitOctonionLiePacket.normNegative = 4 ∧
      realSplitOctonionLiePacket.normZero = 0 ∧
      realSplitOctonionLiePacket.normMultiplicativeSymbolic = true ∧
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
      realSplitOctonionLiePacket.finiteG2TwoOrder = 12096 ∧
      realSplitOctonionLiePacket.dmodulesWeylCommutators = true ∧
      realSplitOctonionLiePacket.dmodulesRootChart = true ∧
      realSplitOctonionLiePacket.dmodulesRootArrangementDegree = 6 ∧
      realSplitOctonionLiePacket.dmodulesHolonomic = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact CA readback for the split-octonion norm form and composition law. -/
theorem norm_signature_and_multiplicativity_packet :
    realSplitOctonionLiePacket.zornUnitTwoSided = true ∧
      realSplitOctonionLiePacket.normPositive = 4 ∧
      realSplitOctonionLiePacket.normNegative = 4 ∧
      realSplitOctonionLiePacket.normZero = 0 ∧
      realSplitOctonionLiePacket.normMultiplicativeSymbolic = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

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

/-- Macaulay2 `Dmodules` exact-root-chart readback. -/
theorem dmodules_root_chart_packet :
    realSplitOctonionLiePacket.dmodulesWeylCommutators = true ∧
      realSplitOctonionLiePacket.dmodulesRootChart = true ∧
      realSplitOctonionLiePacket.dmodulesRootArrangementDegree = 6 ∧
      realSplitOctonionLiePacket.dmodulesHolonomic = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The exact CA packet currently records exact computer algebra for the Lie algebra. -/
theorem current_status_is_exactComputerAlgebraLieAlgebra :
    currentRealClassificationStatus = RealClassificationStatus.exactComputerAlgebraLieAlgebra := by
  rfl

/-- The exact CA packet currently records the Lie-algebra status in a separate lane from the native Lean group equivalence. -/
theorem current_status_records_distinct_group_equivalence_lane :
    currentRealClassificationStatus ≠ RealClassificationStatus.nativeLeanGroupEquivalence := by
  decide

end InfoGeometry.Lie.RealSplitOctonionG2Classification
