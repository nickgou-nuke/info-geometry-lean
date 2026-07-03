import Mathlib.Tactic

/-!
# Split octonion evidence for the flat `(2,3,5)` distribution

This file records the theorem-honest Lean readback of the exact computer-algebra
packet in `tools/infra/split_octonion_235_distribution`.  It does not claim a
native global Cartan geometry construction.  The closed facts here are the
finite-dimensional ranks/dimensions verified from the Zorn product over `QQ`.
-/

namespace InfoGeometry.Lie.SplitOctonion235Distribution

/-- Status labels for the split-octonion `(2,3,5)` lane. -/
inductive Distribution235Status where
  | exactLocalAlgebraEvidence
  | globalCartanGeometryOpenDebt
  deriving DecidableEq, Repr

/-- Evidence packet for the flat split-octonion homogeneous `(2,3,5)` model. -/
structure SplitOctonion235Packet where
  imaginaryDimension : ℕ
  imaginaryNormPositiveNegativeUnordered : ℕ × ℕ
  projectiveNullQuadricDimension : ℕ
  leftAnnihilatorRank : ℕ
  leftAnnihilatorDimension : ℕ
  projectivizedDistributionRank : ℕ
  firstDerivedRank : ℕ
  ambientRank : ℕ
  splitG2SymmetryDimension : ℕ
  status : Distribution235Status

/-- Exact readback from the multi-engine local algebra packet. -/
def splitOctonion235Packet : SplitOctonion235Packet where
  imaginaryDimension := 7
  imaginaryNormPositiveNegativeUnordered := (3, 4)
  projectiveNullQuadricDimension := 5
  leftAnnihilatorRank := 4
  leftAnnihilatorDimension := 3
  projectivizedDistributionRank := 2
  firstDerivedRank := 3
  ambientRank := 5
  splitG2SymmetryDimension := 14
  status := Distribution235Status.exactLocalAlgebraEvidence

/-- The exact local algebra packet has the expected `(2,3,5)` dimensions. -/
theorem splitOctonion235Packet_dimensions :
    splitOctonion235Packet.imaginaryDimension = 7 ∧
      splitOctonion235Packet.imaginaryNormPositiveNegativeUnordered = (3, 4) ∧
      splitOctonion235Packet.projectiveNullQuadricDimension = 5 ∧
      splitOctonion235Packet.leftAnnihilatorDimension = 3 ∧
      splitOctonion235Packet.projectivizedDistributionRank = 2 ∧
      splitOctonion235Packet.firstDerivedRank = 3 ∧
      splitOctonion235Packet.ambientRank = 5 ∧
      splitOctonion235Packet.splitG2SymmetryDimension = 14 := by
  simp [splitOctonion235Packet]

/-- The current packet is local algebra evidence, not a global Cartan-geometry proof. -/
theorem splitOctonion235Packet_not_global_cartan_geometry :
    splitOctonion235Packet.status ≠ Distribution235Status.globalCartanGeometryOpenDebt := by
  decide

end InfoGeometry.Lie.SplitOctonion235Distribution
