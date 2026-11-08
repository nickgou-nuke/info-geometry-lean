import InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier

/-!
# Finite nuclear five-grade, BdG, CAR--CCR, and Soloviev closure

This capstone combines explicit associative operator layers:

1. two-mode CAR with grades `-2,-1,0,1,2`;
2. a grade-preserving representation of named nuclear generators;
3. compression of the CAR pair Hamiltonian to a `2 × 2` BdG block;
4. a common CAR--CCR carrier whose `0,1` occupation compression is the finite
   Soloviev matrix.

It does not identify this concrete model with the generic Freudenthal/TKK
five-graded carrier. That remaining comparison is an intertwiner theorem.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure

open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
open InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
open InfoGeometry.Physics.NuclearBdGSolovievCompression
open InfoGeometry.Physics.NuclearCARPhononCommonCarrier

/-- Exact finite closure packet. -/
theorem finite_nuclear_lane_closure
    (Eqp ω V ξ Δ E : ℂ) :
    (∀ g : Generator, HasGrade (degree g) (represent g)) ∧
    (∀ g h : Generator,
      HasGrade (degree g + degree h)
        (commutator (represent g) (represent h))) ∧
    annihilationOne * creationOne + creationOne * annihilationOne = 1 ∧
    annihilationTwo * creationTwo + creationTwo * annihilationTwo = 1 ∧
    commutator pairCreation pairAnnihilation = gradeCartan ∧
    bdgBlock ξ Δ * bdgBlock ξ Δ =
      (ξ ^ 2 + Δ ^ 2) • (1 : Mat2) ∧
    solovievBlock Eqp ω V =
      (Eqp + ω / 2) • (1 : Mat2) + bdgBlock (ω / 2) V ∧
    Matrix.det (solovievBlock Eqp ω V - E • (1 : Mat2)) =
      (Eqp - E) * (Eqp + ω - E) - V ^ 2 ∧
    pointwiseLift annihilationOne * pointwiseLift creationOne +
      pointwiseLift creationOne * pointwiseLift annihilationOne = 1 ∧
    bosonAnnihilation * bosonCreation -
      bosonCreation * bosonAnnihilation = 1 ∧
    pointwiseLift creationOne * bosonCreation =
      bosonCreation * pointwiseLift creationOne ∧
    ∀ φ : EvenSector,
      compressedOscillatorHamiltonian Eqp ω V φ =
        Matrix.mulVec (solovievBlock Eqp ω V) φ := by
  exact ⟨represent_hasGrade,
    represented_commutator_hasGrade,
    CAR_one,
    CAR_two,
    pairCreation_pairAnnihilation_commutator,
    bdgBlock_sq ξ Δ,
    solovievBlock_eq_center_add_bdg Eqp ω V,
    solovievBlock_characteristic Eqp ω V E,
    common_CAR_one,
    boson_CCR,
    pointwiseLift_commutes_bosonCreation creationOne,
    compressedOscillatorHamiltonian_eq_soloviev Eqp ω V⟩

/-- The finite Soloviev matrix has two exact mathematical origins in the model:
an affine-centered BdG block and an occupation-space compression. -/
theorem soloviev_two_origin_packet (Eqp ω V : ℂ) :
    solovievBlock Eqp ω V =
        (Eqp + ω / 2) • (1 : Mat2) + bdgBlock (ω / 2) V ∧
      ∀ φ : EvenSector,
        compressedOscillatorHamiltonian Eqp ω V φ =
          Matrix.mulVec (solovievBlock Eqp ω V) φ := by
  exact ⟨solovievBlock_eq_center_add_bdg Eqp ω V,
    compressedOscillatorHamiltonian_eq_soloviev Eqp ω V⟩

/-- General bracket closure of the concrete operator grading. -/
theorem finite_operator_five_grade_bracket_closure
    {m n : ℤ} {X Y : Op}
    (hX : HasGrade m X) (hY : HasGrade n Y) :
    HasGrade (m + n) (commutator X Y) :=
  hX.commutator hY

end InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure

