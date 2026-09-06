import Mathlib.Tactic
import InfoGeometry.Algebra.CircularChiralOperatorEightBridge
import InfoGeometry.Clifford.Cl55ZornCARComparison
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.OperatorZornSoldering
import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Projective.FiveGradedCentralizer

/-!
# Circular chiral frame in the native Fock / operator-Zorn carrier

This owner gives a relation-level second-quantized readout of the full eight-slot
circular chiral frame.  It does not identify the full non-associative Zorn
algebra with an associative operator algebra.

The six null rails are represented by the established three-mode Jordan-Wigner
CAR operators.  The two scalar circular poles are represented by the native
complementary Fock chirality projectors `PPlus` and `PMinus`.  The pole
orientation is stated explicitly: projective pole coordinate `1` is the `+2`
endpoint and maps to `PPlus`, while coordinate `0` is the `-2` endpoint and
maps to `PMinus`.

The resulting selected-colour packet is an honest element of the existing
associative `OperatorZornMatrix (MatStage 5)` Nambu--Gorkov shell.
-/

noncomputable section

namespace InfoGeometry.Physics.CircularChiralFockOperatorZornBridge

open InfoGeometry.Algebra.CircularChiralOperatorEightBridge
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.OperatorZornMatrix
open InfoGeometry.Projective.Closure
open InfoGeometry.Canonical.ConformalFiveGradeInversion

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

/-- Index of the positive circular rail `U_i` in the named eight-frame. -/
def positiveFrameIndex (i : Fin 3) : Fin 8 :=
  ⟨i.1 + 1, by omega⟩

/-- Index of the negative circular rail `V_i` in the named eight-frame. -/
def negativeFrameIndex (i : Fin 3) : Fin 8 :=
  ⟨i.1 + 5, by omega⟩

@[simp] theorem operatorFrame_positiveRail (i : Fin 3) :
    operatorFrame (positiveFrameIndex i) = U i := by
  fin_cases i <;> rfl

@[simp] theorem operatorFrame_negativeRail (i : Fin 3) :
    operatorFrame (negativeFrameIndex i) = V i := by
  fin_cases i <;> rfl

/-- Native second-quantized readout of a positive circular/root-plus channel.
The repository convention identifies positive roots with annihilation. -/
def positiveRailFock (i : Fin 3) : FockOp :=
  f (firstThreeIndex i)

/-- Native second-quantized readout of a negative circular/root-minus channel.
The repository convention identifies negative roots with creation. -/
def negativeRailFock (i : Fin 3) : FockOp :=
  e (firstThreeIndex i)

@[simp] theorem positiveRailFock_sq (i : Fin 3) :
    positiveRailFock i * positiveRailFock i = 0 := by
  exact f_sq (firstThreeIndex i)

@[simp] theorem negativeRailFock_sq (i : Fin 3) :
    negativeRailFock i * negativeRailFock i = 0 := by
  exact e_sq (firstThreeIndex i)

theorem positiveRailFock_anticomm (i j : Fin 3) :
    positiveRailFock i * positiveRailFock j +
      positiveRailFock j * positiveRailFock i = 0 := by
  exact f_anticomm (firstThreeIndex i) (firstThreeIndex j)

theorem negativeRailFock_anticomm (i j : Fin 3) :
    negativeRailFock i * negativeRailFock j +
      negativeRailFock j * negativeRailFock i = 0 := by
  exact e_anticomm (firstThreeIndex i) (firstThreeIndex j)

theorem positive_negativeRailFock_CAR (i j : Fin 3) :
    positiveRailFock i * negativeRailFock j +
      negativeRailFock j * positiveRailFock i =
        if i = j then (1 : FockOp) else 0 := by
  have h := ef_car (firstThreeIndex j) (firstThreeIndex i)
  rw [add_comm] at h
  by_cases hij : i = j
  · subst j
    simpa [positiveRailFock, negativeRailFock] using h
  · have hidx : firstThreeIndex j ≠ firstThreeIndex i := by
      intro hji
      exact hij (firstThreeIndex_injective hji.symm)
    simpa [positiveRailFock, negativeRailFock, hij, hidx] using h

/-! ## Scalar circular poles -/

/-- Second-quantized readout of the positive circular scalar pole `E11 = u+`. -/
def circularFockScalarPlus : FockOp := PPlus

/-- Second-quantized readout of the negative circular scalar pole `E22 = u-`. -/
def circularFockScalarMinus : FockOp := PMinus

@[simp] theorem circularFockScalarPlus_sq :
    circularFockScalarPlus * circularFockScalarPlus = circularFockScalarPlus := by
  exact PPlus_sq

@[simp] theorem circularFockScalarMinus_sq :
    circularFockScalarMinus * circularFockScalarMinus = circularFockScalarMinus := by
  exact PMinus_sq

@[simp] theorem circularFockScalarPlus_mul_minus :
    circularFockScalarPlus * circularFockScalarMinus = 0 := by
  exact PPlus_mul_PMinus

@[simp] theorem circularFockScalarPlus_add_minus :
    circularFockScalarPlus + circularFockScalarMinus = 1 := by
  exact P_sum

/-- The source scalar poles are exactly the two endpoints of the named circular
operator frame. -/
theorem circular_scalar_source_readout :
    operatorFrame 0 = E11 ∧ operatorFrame 4 = E22 := by
  constructor <;> simp [operatorFrame]

/-- Projective pole labels are oriented explicitly: coordinate `1` is the `+2`
endpoint and coordinate `0` is the `-2` endpoint. -/
def fockPoleProjector (i : Fin 2) : FockOp :=
  if i = 0 then circularFockScalarMinus else circularFockScalarPlus

@[simp] theorem fockPoleProjector_zero :
    fockPoleProjector 0 = circularFockScalarMinus := by
  simp [fockPoleProjector]

@[simp] theorem fockPoleProjector_one :
    fockPoleProjector 1 = circularFockScalarPlus := by
  simp [fockPoleProjector]

/-- Möbius/five-grade inversion swaps the two Fock pole projectors. -/
theorem fockPoleProjector_conformalSwap (i : Fin 2) :
    fockPoleProjector (conformalPoleSwap2 i) =
      if i = 0 then circularFockScalarPlus else circularFockScalarMinus := by
  fin_cases i <;> simp [fockPoleProjector, conformalPoleSwap2]

/-- The positive Fock scalar pole carries the projective `+2` endpoint label. -/
theorem circularFockScalarPlus_grade :
    conformalPoleGrade2 (1 : Fin 2) = ConformalGrade.posTwo := by
  exact conformalPoleGrade2_one

/-- The negative Fock scalar pole carries the projective `-2` endpoint label. -/
theorem circularFockScalarMinus_grade :
    conformalPoleGrade2 (0 : Fin 2) = ConformalGrade.negTwo := by
  exact conformalPoleGrade2_zero

/-- The projective inversion reverses the extremal five-grade label while the
Fock readout swaps the complementary scalar projectors. -/
theorem fockPole_fiveGrade_inversion_packet (i : Fin 2) :
    conformalPoleGrade2 (conformalPoleSwap2 i) =
        ConformalGrade.swap (conformalPoleGrade2 i) ∧
    fockPoleProjector (conformalPoleSwap2 i) =
        (if i = 0 then circularFockScalarPlus else circularFockScalarMinus) := by
  exact ⟨conformalPoleGrade2_swap i, fockPoleProjector_conformalSwap i⟩

/-! ## Finite log-scale / chiral grading readout -/

/-- Difference of the complementary pole projectors.  In the native Fock
representation it is exactly the spinor chirality operator. -/
def poleLogScaleGenerator : FockOp :=
  circularFockScalarPlus - circularFockScalarMinus

@[simp] theorem poleLogScaleGenerator_eq_gammaChiral :
    poleLogScaleGenerator = gammaChiral := by
  simp [poleLogScaleGenerator, circularFockScalarPlus,
    circularFockScalarMinus, PPlus, PMinus]
  module

/-- The positive pole is the `+1` eigensector of the finite log-scale grading. -/
theorem poleLogScaleGenerator_mul_plus :
    poleLogScaleGenerator * circularFockScalarPlus = circularFockScalarPlus := by
  rw [poleLogScaleGenerator_eq_gammaChiral]
  simp [circularFockScalarPlus, PPlus]
  rw [gammaChiral_sq]
  module

/-- The negative pole is the `-1` eigensector of the finite log-scale grading. -/
theorem poleLogScaleGenerator_mul_minus :
    poleLogScaleGenerator * circularFockScalarMinus = -circularFockScalarMinus := by
  rw [poleLogScaleGenerator_eq_gammaChiral]
  simp [circularFockScalarMinus, PMinus]
  rw [gammaChiral_sq]
  module

/-- The pole projectors commute with the finite log-scale grading. -/
theorem poleLogScaleGenerator_commutes_poles :
    poleLogScaleGenerator * circularFockScalarPlus =
        circularFockScalarPlus * poleLogScaleGenerator ∧
      poleLogScaleGenerator * circularFockScalarMinus =
        circularFockScalarMinus * poleLogScaleGenerator := by
  rw [poleLogScaleGenerator_eq_gammaChiral]
  constructor
  · simp [circularFockScalarPlus, PPlus]
    rw [gammaChiral_sq]
    module
  · simp [circularFockScalarMinus, PMinus]
    rw [gammaChiral_sq]
    module

/-! ## Full second-quantized circular packet -/

/-- Full eight-channel second-quantized packet: complementary scalar projectors
and the three annihilation/creation rails. -/
def circularFockPacket : ChiralSigmaOperatorPacket FockOp where
  uPlus := circularFockScalarPlus
  uMinus := circularFockScalarMinus
  sigmaPlus := positiveRailFock
  sigmaMinus := negativeRailFock

/-- Colour selection of the three circular rails. -/
def colourSoldering (c : Fin 3) : ChiralSigmaSoldering FockOp FockOp where
  plus rail := rail c
  minus rail := rail c

/-- Full selected-colour operator-Zorn/Nambu--Gorkov packet.  Unlike the generic
rail-only soldering helper, the diagonal scalar pole entries are retained. -/
def circularColourOperatorZorn (c : Fin 3) : OperatorZornMatrix FockOp where
  n_plus_op := circularFockPacket.uPlus
  n_minus_op := circularFockPacket.uMinus
  sigma_plus_op := (colourSoldering c).plus circularFockPacket.sigmaPlus
  sigma_minus_op := (colourSoldering c).minus circularFockPacket.sigmaMinus

@[simp] theorem circularColourOperatorZorn_n_plus (c : Fin 3) :
    (circularColourOperatorZorn c).n_plus_op = circularFockScalarPlus := rfl

@[simp] theorem circularColourOperatorZorn_n_minus (c : Fin 3) :
    (circularColourOperatorZorn c).n_minus_op = circularFockScalarMinus := rfl

@[simp] theorem circularColourOperatorZorn_sigma_plus (c : Fin 3) :
    (circularColourOperatorZorn c).sigma_plus_op = positiveRailFock c := rfl

@[simp] theorem circularColourOperatorZorn_sigma_minus (c : Fin 3) :
    (circularColourOperatorZorn c).sigma_minus_op = negativeRailFock c := rfl

/-- Matrix readback of the full selected second-quantized circular packet. -/
theorem circularColourOperatorZorn_toMatrix (c : Fin 3) :
    OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) =
      !![circularFockScalarPlus, positiveRailFock c;
         negativeRailFock c, circularFockScalarMinus] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Real split four-potential compression -/

/-- A real operator-valued four-potential on the finite Fock algebra.  This is
the bilingual real/split counterpart of the complex `OperatorFourVector`: the
four entries are operator coefficients rather than scalar spacetime numbers. -/
abbrev RealOperatorFourPotential := Fin 4 → FockOp

/-- Compression of one selected colour of the full `1+3+3+1` circular packet
into four real operator coordinates.

`v₀,v₃` are the half-sum/half-difference of the two scalar sheets, while
`v₁,v₂` are the symmetric/antisymmetric combinations of annihilation and
creation.  Thus the complex notation `v₁ ∓ i v₂` is replaced by the real split
pair `v₁ ∓ v₂`. -/
def circularCompressedFourPotential (c : Fin 3) : RealOperatorFourPotential
  | 0 => (1 / 2 : ℝ) • (circularFockScalarPlus + circularFockScalarMinus)
  | 1 => (1 / 2 : ℝ) • (positiveRailFock c + negativeRailFock c)
  | 2 => (1 / 2 : ℝ) • (negativeRailFock c - positiveRailFock c)
  | 3 => (1 / 2 : ℝ) • (circularFockScalarPlus - circularFockScalarMinus)

/-- Real split soldering of four operator coordinates into a `2×2` matrix.
It is the no-external-`i` counterpart of Pauli/Dirac soldering. -/
def realSplitFourSoldering (v : RealOperatorFourPotential) :
    Matrix (Fin 2) (Fin 2) FockOp :=
  !![v 0 + v 3, v 1 - v 2;
     v 1 + v 2, v 0 - v 3]

@[simp] theorem circularCompressedFourPotential_scalar (c : Fin 3) :
    circularCompressedFourPotential c 0 = (1 / 2 : ℝ) • (1 : FockOp) := by
  simp [circularCompressedFourPotential, circularFockScalarPlus_add_minus]

@[simp] theorem circularCompressedFourPotential_chiral (c : Fin 3) :
    circularCompressedFourPotential c 3 = (1 / 2 : ℝ) • gammaChiral := by
  rw [show circularCompressedFourPotential c 3 =
      (1 / 2 : ℝ) • poleLogScaleGenerator by rfl]
  rw [poleLogScaleGenerator_eq_gammaChiral]

/-- The two diagonal sheet coordinates reconstruct exactly the two circular
Fock projectors. -/
theorem circularCompressedFourPotential_diagonal_reconstruction (c : Fin 3) :
    circularCompressedFourPotential c 0 + circularCompressedFourPotential c 3 =
        circularFockScalarPlus ∧
      circularCompressedFourPotential c 0 - circularCompressedFourPotential c 3 =
        circularFockScalarMinus := by
  constructor <;>
    simp [circularCompressedFourPotential] <;> module

/-- The symmetric/antisymmetric rail coordinates reconstruct exactly the
annihilation and creation channels. -/
theorem circularCompressedFourPotential_offDiagonal_reconstruction (c : Fin 3) :
    circularCompressedFourPotential c 1 - circularCompressedFourPotential c 2 =
        positiveRailFock c ∧
      circularCompressedFourPotential c 1 + circularCompressedFourPotential c 2 =
        negativeRailFock c := by
  constructor <;>
    simp [circularCompressedFourPotential] <;> module

/-- Main compression theorem: the real split four-potential is exactly the
`2×2` associative shell of the selected full `1+3+3+1` second-quantized
circular packet. -/
theorem realSplitFourSoldering_eq_circularOperatorZorn (c : Fin 3) :
    realSplitFourSoldering (circularCompressedFourPotential c) =
      OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) := by
  rw [circularColourOperatorZorn_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSplitFourSoldering, circularCompressedFourPotential] <;> module

/-- Compact statement that the full circular packet is an eight-channel
`1+3+3+1` object whose selected-colour associative shell is faithfully
reconstructed from four real operator coordinates. -/
theorem circular_1331_compressed_four_potential_packet (c : Fin 3) :
    circularFockPacket.uPlus = circularFockScalarPlus ∧
    circularFockPacket.uMinus = circularFockScalarMinus ∧
    (∀ i : Fin 3, circularFockPacket.sigmaPlus i = positiveRailFock i) ∧
    (∀ i : Fin 3, circularFockPacket.sigmaMinus i = negativeRailFock i) ∧
    realSplitFourSoldering (circularCompressedFourPotential c) =
      OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) := by
  exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl,
    realSplitFourSoldering_eq_circularOperatorZorn c⟩

/-- Compact full-frame packet: scalar poles reproduce the complementary Fock
projector algebra and the six rails reproduce the three-mode CAR routing. -/
theorem circular_chiral_fock_operatorZorn_packet (c : Fin 3) :
    operatorFrame 0 = E11 ∧
    operatorFrame 4 = E22 ∧
    circularFockScalarPlus * circularFockScalarPlus = circularFockScalarPlus ∧
    circularFockScalarMinus * circularFockScalarMinus = circularFockScalarMinus ∧
    circularFockScalarPlus * circularFockScalarMinus = 0 ∧
    circularFockScalarPlus + circularFockScalarMinus = 1 ∧
    operatorFrame (positiveFrameIndex c) = U c ∧
    operatorFrame (negativeFrameIndex c) = V c ∧
    positiveRailFock c * positiveRailFock c = 0 ∧
    negativeRailFock c * negativeRailFock c = 0 ∧
    positiveRailFock c * negativeRailFock c +
      negativeRailFock c * positiveRailFock c = (1 : FockOp) ∧
    OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) =
      !![circularFockScalarPlus, positiveRailFock c;
         negativeRailFock c, circularFockScalarMinus] := by
  exact ⟨(circular_scalar_source_readout).1,
    (circular_scalar_source_readout).2,
    circularFockScalarPlus_sq,
    circularFockScalarMinus_sq,
    circularFockScalarPlus_mul_minus,
    circularFockScalarPlus_add_minus,
    operatorFrame_positiveRail c,
    operatorFrame_negativeRail c,
    positiveRailFock_sq c,
    negativeRailFock_sq c,
    positive_negativeRailFock_CAR c c,
    circularColourOperatorZorn_toMatrix c⟩

end InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
