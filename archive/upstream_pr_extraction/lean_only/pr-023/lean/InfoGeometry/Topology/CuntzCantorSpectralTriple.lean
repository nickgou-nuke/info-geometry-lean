import Mathlib
import InfoGeometry.OperatorAlgebra.ErlangenNet
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Topology

/-!
# Cuntz/Cantor spectral triple socket

This file gives a theorem-safe analytic socket for turning the symbolic binary
boundary of `ErlangenNet` into an operator-algebraic carrier.

The module deliberately separates four layers:

* a binary symbolic boundary `N -> BinarySector`;
* Cuntz `O_2`-style isometry data on an abstract star algebra;
* candidate Majorana/Clifford operators built from shifts;
* a witness-gated Cantor spectral-triple packet.

Guardrail: the Cuntz relations alone do not prove that `S + S*` is a Clifford
unitary. The CAR/Clifford laws are therefore carried by explicit witnesses.
Likewise, the Dirac operator and Hausdorff-dimension readout are supplied as
spectral-triple data, not derived from the Cuntz carrier alone.
-/

open InfoGeometry.OperatorAlgebra.ErlangenNet

/-- Binary Cantor boundary used by the operator-Erlangen net. -/
abbrev BinaryCantorBoundary := SectorBoundary BinarySector

/-- Finite binary cylinder word of depth `n`. -/
abbrev BinaryCylinder (n : Nat) := FiniteSectorWord BinarySector n

/-- Prefixing a binary symbol to an infinite Cantor code. -/
@[rep_depth operator]
def prefixBoundary (s : BinarySector) (x : BinaryCantorBoundary) : BinaryCantorBoundary
    | 0 => s
    | n + 1 => x n

@[rep_depth operator]
theorem prefixBoundary_zero
    (s : BinarySector) (x : BinaryCantorBoundary) :
    prefixBoundary s x 0 = s :=
  rfl

@[rep_depth operator]
theorem prefixBoundary_succ
    (s : BinarySector) (x : BinaryCantorBoundary) (n : Nat) :
    prefixBoundary s x (n + 1) = x n :=
  rfl

/-- Abstract Cuntz `O_2` carrier in a star ring. -/
@[rep_depth operator]
structure CuntzO2Carrier
    (Op : Type*) [Ring Op] [StarRing Op] where
  S_left : Op
  S_right : Op

  left_isometry :
    star S_left * S_left = 1

  right_isometry :
    star S_right * S_right = 1

  orthogonal_ranges :
    star S_left * S_right = 0 ∧ star S_right * S_left = 0

  range_sum :
    S_left * star S_left + S_right * star S_right = 1

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzO2Carrier Op)

/-- Left range projection `S_1 S_1*`. -/
@[rep_depth operator]
def leftRangeProjection : Op :=
  C.S_left * star C.S_left

/-- Right range projection `S_2 S_2*`. -/
@[rep_depth operator]
def rightRangeProjection : Op :=
  C.S_right * star C.S_right

/-- The two range projections sum to the identity by the Cuntz relation. -/
@[rep_depth operator]
theorem rangeProjection_sum_one :
    C.leftRangeProjection + C.rightRangeProjection = 1 := by
  exact C.range_sum

/-- Left range projection is idempotent. -/
@[rep_depth operator]
theorem leftRangeProjection_idempotent :
    C.leftRangeProjection * C.leftRangeProjection = C.leftRangeProjection := by
  unfold leftRangeProjection
  calc
    (C.S_left * star C.S_left) * (C.S_left * star C.S_left)
        = C.S_left * (star C.S_left * C.S_left) * star C.S_left := by
          noncomm_ring
    _ = C.S_left * 1 * star C.S_left := by
          rw [C.left_isometry]
    _ = C.S_left * star C.S_left := by
          simp

/-- Right range projection is idempotent. -/
@[rep_depth operator]
theorem rightRangeProjection_idempotent :
    C.rightRangeProjection * C.rightRangeProjection = C.rightRangeProjection := by
  unfold rightRangeProjection
  calc
    (C.S_right * star C.S_right) * (C.S_right * star C.S_right)
        = C.S_right * (star C.S_right * C.S_right) * star C.S_right := by
          noncomm_ring
    _ = C.S_right * 1 * star C.S_right := by
          rw [C.right_isometry]
    _ = C.S_right * star C.S_right := by
          simp

/-- The left and right range projections are orthogonal on the left product. -/
@[rep_depth operator]
theorem leftRange_mul_rightRange_eq_zero :
    C.leftRangeProjection * C.rightRangeProjection = 0 := by
  unfold leftRangeProjection rightRangeProjection
  calc
    (C.S_left * star C.S_left) * (C.S_right * star C.S_right)
        = C.S_left * (star C.S_left * C.S_right) * star C.S_right := by
          noncomm_ring
    _ = C.S_left * 0 * star C.S_right := by
          rw [C.orthogonal_ranges.1]
    _ = 0 := by
          simp

/-- The left and right range projections are orthogonal on the right product. -/
@[rep_depth operator]
theorem rightRange_mul_leftRange_eq_zero :
    C.rightRangeProjection * C.leftRangeProjection = 0 := by
  unfold leftRangeProjection rightRangeProjection
  calc
    (C.S_right * star C.S_right) * (C.S_left * star C.S_left)
        = C.S_right * (star C.S_right * C.S_left) * star C.S_left := by
          noncomm_ring
    _ = C.S_right * 0 * star C.S_left := by
          rw [C.orthogonal_ranges.2]
    _ = 0 := by
          simp

end CuntzO2Carrier

/-- Candidate Majorana/Clifford operators generated from a Cuntz shift. -/
@[rep_depth operator]
structure CuntzMajoranaCandidates
    (Op : Type*) [Ring Op] [StarRing Op] [SMul ℂ Op] where
  cuntz : CuntzO2Carrier Op
  phaseI : ℂ
  phaseI_eq : phaseI = Complex.I

namespace CuntzMajoranaCandidates

variable {Op : Type*} [Ring Op] [StarRing Op] [SMul ℂ Op]
variable (M : CuntzMajoranaCandidates Op)

/-- Candidate `e_1 = S_1 + S_1*`. -/
@[rep_depth operator]
def e1 : Op :=
  M.cuntz.S_left + star M.cuntz.S_left

/-- Candidate `e_2 = i • (S_1 - S_1*)`. -/
@[rep_depth operator]
def e2 : Op :=
  M.phaseI • (M.cuntz.S_left - star M.cuntz.S_left)

@[rep_depth operator]
theorem e1_eq :
    M.e1 = M.cuntz.S_left + star M.cuntz.S_left :=
  rfl

@[rep_depth operator]
theorem e2_eq :
    M.e2 = M.phaseI • (M.cuntz.S_left - star M.cuntz.S_left) :=
  rfl

end CuntzMajoranaCandidates

/-- Anticommutator in an abstract ring. -/
@[rep_depth operator]
def anticommutator
    {Op : Type*} [Add Op] [Mul Op]
    (x y : Op) : Op :=
  x * y + y * x

/--
Witness that the Cuntz Majorana candidates satisfy the intended Clifford/CAR laws.

This is intentionally not derived from the Cuntz relations alone.
-/
@[rep_depth operator]
structure MajoranaCARWitness
    (Op : Type*) [Ring Op] [StarRing Op] [SMul ℂ Op]
    (M : CuntzMajoranaCandidates Op) where
  e1_square :
    M.e1 * M.e1 = 1

  e2_square :
    M.e2 * M.e2 = 1

  anticommute :
    anticommutator M.e1 M.e2 = 0

/-- A bounded spectral-triple-style socket over a Cuntz/Cantor carrier. -/
@[rep_depth operator]
structure CuntzCantorSpectralTriple
    (Op H : Type*) [Ring Op] [StarRing Op] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [SMul Op H] where
  cuntz : CuntzO2Carrier Op

  /-- Representation of the binary Cantor cylinder algebra in the operator carrier. -/
  cylinderRepresentation : (n : Nat) -> BinaryCylinder n -> Op

  /-- Bounded placeholder for a Dirac/supercharge operator. -/
  dirac : H →L[ℂ] H

  /-- Representation action used to state bounded commutator data. -/
  representedAction : Op -> H →L[ℂ] H

  /-- Supplied bounded-commutator condition for represented cylinder operators. -/
  boundedCommutatorWitness : Prop
  boundedCommutatorCertified : boundedCommutatorWitness

  /-- Supplied compact-resolvent or summability condition. -/
  compactResolventOrSummability : Prop
  compactResolventOrSummabilityCertified : compactResolventOrSummability

  /-- Spectral dimension readout supplied by the concrete model. -/
  spectralDimension : ℝ

  /-- Optional calibration to the middle-thirds Cantor dimension. -/
  cantorDimensionCalibration :
    spectralDimension = Real.log 2 / Real.log 3

namespace CuntzCantorSpectralTriple

variable {Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
variable (T : CuntzCantorSpectralTriple Op H)

/-- The left Cuntz range projection of the spectral-triple carrier. -/
@[rep_depth operator]
def leftCylinderProjection : Op :=
  T.cuntz.leftRangeProjection

/-- The right Cuntz range projection of the spectral-triple carrier. -/
@[rep_depth operator]
def rightCylinderProjection : Op :=
  T.cuntz.rightRangeProjection

/-- Cylinder projections cover the binary boundary at the first level. -/
@[rep_depth operator]
theorem firstLevelCylinder_sum_one :
    T.leftCylinderProjection + T.rightCylinderProjection = 1 := by
  exact T.cuntz.rangeProjection_sum_one

/-- The supplied spectral dimension equals the middle-thirds Cantor dimension. -/
@[rep_depth operator]
theorem spectralDimension_eq_middleThirdsCantor :
    T.spectralDimension = Real.log 2 / Real.log 3 :=
  T.cantorDimensionCalibration

/-- Re-export the bounded-commutator witness. -/
@[rep_depth operator]
theorem boundedCommutator_holds :
    T.boundedCommutatorWitness :=
  T.boundedCommutatorCertified

/-- Re-export the compact-resolvent/summability witness. -/
@[rep_depth operator]
theorem compactResolventOrSummability_holds :
    T.compactResolventOrSummability :=
  T.compactResolventOrSummabilityCertified

end CuntzCantorSpectralTriple

/--
Connection socket from a combinatorial `ErlangenNet` boundary to a Cuntz/Cantor
spectral triple.
-/
@[rep_depth operator]
structure ErlangenNetCuntzRealization
    (Alg Frame Sym Label Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] where
  net : IteratedObservableSectorization Alg Frame Sym BinarySector Label
  triple : CuntzCantorSpectralTriple Op H

  /-- Boundary-code prefixing is represented by the left Cuntz shift. -/
  leftPrefixRealization : Prop
  leftPrefixRealizationCertified : leftPrefixRealization

  /-- Boundary-code prefixing is represented by the right Cuntz shift. -/
  rightPrefixRealization : Prop
  rightPrefixRealizationCertified : rightPrefixRealization

namespace ErlangenNetCuntzRealization

variable {Alg Frame Sym Label Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
variable (R : ErlangenNetCuntzRealization Alg Frame Sym Label Op H)

/-- Re-export the left-prefix realization witness. -/
@[rep_depth operator]
theorem leftPrefixRealization_holds :
    R.leftPrefixRealization :=
  R.leftPrefixRealizationCertified

/-- Re-export the right-prefix realization witness. -/
@[rep_depth operator]
theorem rightPrefixRealization_holds :
    R.rightPrefixRealization :=
  R.rightPrefixRealizationCertified

/-- The Cuntz realization gives the first-level boundary decomposition. -/
@[rep_depth operator]
theorem realized_firstLevelCylinder_sum_one :
    R.triple.leftCylinderProjection + R.triple.rightCylinderProjection = 1 :=
  R.triple.firstLevelCylinder_sum_one

end ErlangenNetCuntzRealization

end InfoGeometry.Topology
