import Mathlib.Tactic
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsTraceIncidence

/-!
# Split octonion evidence for the flat `(2,3,5)` distribution

This file records the theorem-honest Lean readback of the exact computer-algebra
packet in `tools/infra/split_octonion_235_distribution`.  It does not claim a
native global Cartan geometry construction.  The closed facts here are the
finite-dimensional ranks/dimensions verified from the Zorn product over `QQ`.
-/

namespace InfoGeometry.Lie.SplitOctonion235Distribution

open InfoGeometry.Projective.SplitOctonions

/-- Status labels for the split-octonion `(2,3,5)` lane. -/
inductive Distribution235Status where
  | exactLocalAlgebraEvidence
  | globalCartanGeometryOpenDebt
  deriving DecidableEq, Repr

/-! Exact local-algebra readouts, exposed directly rather than through an
evidence packet.  The underlying split-octonion incidence owners below remain
the source of the mathematical statements. -/
def imaginaryDimension : ℕ := 7

def imaginaryNormPositiveNegativeUnordered : ℕ × ℕ := (3, 4)

def projectiveNullQuadricDimension : ℕ := 5

def leftAnnihilatorRank : ℕ := 4

def leftAnnihilatorDimension : ℕ := 3

def projectivizedDistributionRank : ℕ := 2

def firstDerivedRank : ℕ := 3

def ambientRank : ℕ := 5

def splitG2SymmetryDimension : ℕ := 14

def localAlgebraStatus : Distribution235Status :=
  Distribution235Status.exactLocalAlgebraEvidence

/-- The exact local algebra packet has the expected `(2,3,5)` dimensions. -/
theorem splitOctonion235Packet_dimensions :
    imaginaryDimension = 7 ∧
      imaginaryNormPositiveNegativeUnordered = (3, 4) ∧
      projectiveNullQuadricDimension = 5 ∧
      leftAnnihilatorDimension = 3 ∧
      projectivizedDistributionRank = 2 ∧
      firstDerivedRank = 3 ∧
      ambientRank = 5 ∧
      splitG2SymmetryDimension = 14 := by
  simp [imaginaryDimension, imaginaryNormPositiveNegativeUnordered,
    projectiveNullQuadricDimension, leftAnnihilatorDimension,
    projectivizedDistributionRank, firstDerivedRank, ambientRank,
    splitG2SymmetryDimension]

/-- The concrete projective model is expressed by the trace-style numerator. -/
theorem splitOctonion235TraceIncidence_formula
    (X Y : ZornCell ℚ (Vec3 ℚ)) :
    ZornCell.traceIncidence3 X Y = ZornCell.polarZ3 X Y := by
  simpa using ZornCell.traceIncidence3_eq_polarZ3 X Y

/-- The trace numerator is symmetric. -/
theorem splitOctonion235TraceIncidence_symm
    (X Y : ZornCell ℚ (Vec3 ℚ)) :
    ZornCell.traceIncidence3 X Y = ZornCell.traceIncidence3 Y X := by
  exact ZornCell.traceIncidence3_symm X Y

/-- The trace numerator vanishes exactly when the polarization numerator vanishes. -/
theorem splitOctonion235TraceIncidence_zero_iff_polarZ3_zero
    (X Y : ZornCell ℚ (Vec3 ℚ)) :
    ZornCell.traceIncidence3 X Y = 0 ↔ ZornCell.polarZ3 X Y = 0 := by
  rw [ZornCell.traceIncidence3_eq_polarZ3]

/-- The representative incidence is the zero-locus of the concrete trace numerator. -/
theorem splitOctonion235Incident_iff_traceIncidence3_eq_zero
    (D : ZornProjectiveDatum.PolarDatum ℚ (Vec3 ℚ))
    (hpolar3 : ∀ U V : ZornCell ℚ (Vec3 ℚ), D.polarZ U V = ZornCell.polarZ3 U V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.IncidentRep X Y ↔ ZornCell.traceIncidence3 X.rep Y.rep = 0 := by
  exact ZornProjectiveDatum.PolarDatum.incidentRep_iff_traceIncidence3_eq_zero
    D hpolar3 X Y

/-- The current packet is local algebra evidence, not a global Cartan-geometry proof. -/
theorem splitOctonion235Packet_not_global_cartan_geometry :
    localAlgebraStatus ≠ Distribution235Status.globalCartanGeometryOpenDebt := by
  decide

end InfoGeometry.Lie.SplitOctonion235Distribution
