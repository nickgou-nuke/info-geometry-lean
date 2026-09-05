import InfoGeometry.Quantum.KramersPhaseGlideRepresentation
import InfoGeometry.Topology.KleinAffineOrbitQuotient
import InfoGeometry.Clifford.O55FiveGradeKramersBridge
import InfoGeometry.Clifford.Pin55KramersContactMultigrading

/-!
# Kramers, Klein, Pin(5,5), and five-grade closure

This capstone keeps four distinct structures typed separately:

* the complex antiunitary Kramers operator;
* the affine Klein deck group and its orbit quotient;
* the native Clifford `Cl(5,5)` five-grading and grade inversion;
* the independent symplectic-pair `ℤ₂` grading of `o(5,5)`.

The exact bridges are grade reversal, phase inversion, and shared parity
readouts.  No equality between an antiunitary, a deck transformation, and a
Pin-group element is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.Pin55KramersKleinFiveGradeClosure

open InfoGeometry.Quantum.ComplexKramersAntiunitary
open InfoGeometry.Quantum.KramersPhaseGlideRepresentation
open InfoGeometry.Quantum.FiveGradedKramersModule
open InfoGeometry.Topology.KleinDeckNormalForm
open InfoGeometry.Topology.KleinAffineOrbitQuotient
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Clifford.O55FiveGradeKramersBridge
open InfoGeometry.Clifford.O55SymmetricBlockGrading
open InfoGeometry.Clifford.Pin55KramersContactMultigrading
open InfoGeometry.Exceptional.Freudenthal

/-- Complex antiunitary and unit-phase inversion packet. -/
theorem complex_kramers_phase_packet
    {z : ℂ} (hunit : star z * z = 1) (v : H2) :
    standardInner (timeReversal v) (timeReversal v) =
        standardInner v v ∧
      standardInner v (timeReversal v) = 0 ∧
      timeReversal (timeReversal v) = -v ∧
      timeReversal (phaseEnd z v) =
        phaseEnd z⁻¹ (timeReversal v) := by
  exact ⟨timeReversal_antiunitary v v,
    timeReversal_kramers_orthogonal v,
    timeReversal_sq v,
    kramers_phase_inverse hunit v⟩

/-- Affine quotient and algebraic `ℤ ⊕ ℤ₂` readout packet.  The readout is not
renamed as singular homology until the universal abelianization and covering
comparison are supplied. -/
theorem klein_quotient_readout_packet :
    b * a * b⁻¹ = a⁻¹ ∧
      (∀ g p, deckAct g p = p ↔ g = 1) ∧
      Function.Surjective abelianReadout ∧
      (2 : ℕ) • abelianReadout a = 0 ∧
      Function.Surjective quotientMap ∧
      Topology.IsQuotientMap quotientMap ∧
      (∀ g p, quotientMap (deckAct g p) = quotientMap p) := by
  exact ⟨klein_conjugation_relation,
    deckAct_eq_self_iff,
    abelianReadout_surjective,
    horizontal_class_order_two,
    quotientMap_surjective,
    quotientMap_isQuotient,
    quotientMap_deckAct⟩

/-- Native `Cl(5,5)` five-grade inversion and complex Kramers reversal share
one grade permutation while retaining different squares. -/
theorem o55_kramers_grade_packet
    (g : ConformalGrade) (x : Alg 5)
    (hx : x ∈ gradeSpace g) (v : H2) :
    thetaOp x ∈ gradeSpace g.swap ∧
      HasGrade (-toInt g)
        (kramers (includeConformalGrade g v)) ∧
      o55FiveParity g.swap = o55FiveParity g ∧
      kramers (kramers (includeConformalGrade g v)) =
        -includeConformalGrade g v :=
  o55_five_grade_kramers_packet g x hx v

/-- The independent `o(5,5)` symmetric-pair grading. -/
theorem o55_symmetric_pair_packet :
    splitMetric * splitMetric = (1 : Mat55) ∧
      (∀ X Y, IsO55Even X → IsO55Even Y →
        IsO55Even (commutator X Y)) ∧
      (∀ X Y, IsO55Even X → IsO55Odd Y →
        IsO55Odd (commutator X Y)) ∧
      (∀ X Y, IsO55Odd X → IsO55Odd Y →
        IsO55Even (commutator X Y)) ∧
      fullEvenGeneratorCount = 20 ∧
      fullOddGeneratorCount = 25 := by
  exact ⟨splitMetric_sq,
    fun _ _ hX hY => o55_even_even hX hY,
    fun _ _ hX hY => o55_even_odd hX hY,
    fun _ _ hX hY => o55_odd_odd hX hY,
    full_even_generator_count_eq,
    full_odd_generator_count_eq⟩

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D₀ : CubicJordanDatum J)

/-- The corrected Freudenthal contact algebra contributes a second genuine
integer five-grading, with its own derived parity.  Only the label-level
correspondence with the O(5,5) conformal grading is asserted here. -/
theorem contact_multiple_grading_packet
    {k l : ℤ} {u v : FiveGradedCarrier D₀}
    (hu : u ∈ symplecticContactGradeSpace D₀ k)
    (hv : v ∈ symplecticContactGradeSpace D₀ l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D₀ (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l ∧
      contactParity (-k) = contactParity k :=
  contact_integer_parity_grading_packet D₀ hu hv

/-- Final finite formalism packet. -/
theorem pin55_kramers_klein_five_grade_packet
    (g : ConformalGrade) (x : Alg 5)
    (hx : x ∈ gradeSpace g) (v : H2) :
    standardInner v (timeReversal v) = 0 ∧
      timeReversal (timeReversal v) = -v ∧
      thetaOp x ∈ gradeSpace g.swap ∧
      HasGrade (-toInt g)
        (kramers (includeConformalGrade g v)) ∧
      o55FiveParity g.swap = o55FiveParity g ∧
      fullEvenGeneratorCount = 20 ∧
      fullOddGeneratorCount = 25 ∧
      PinO55GlideReflection.crosscapOrientationSign = -1 ∧
      b * a * b⁻¹ = a⁻¹ ∧
      Function.Surjective abelianReadout := by
  exact ⟨timeReversal_kramers_orthogonal v,
    timeReversal_sq v,
    theta_maps g x hx,
    (kramers_o55_grade_parity_packet g v).1,
    o55FiveParity_swap g,
    full_even_generator_count_eq,
    full_odd_generator_count_eq,
    PinO55GlideReflection.crosscap_orientation_reversing,
    klein_conjugation_relation,
    abelianReadout_surjective⟩

end InfoGeometry.Clifford.Pin55KramersKleinFiveGradeClosure
