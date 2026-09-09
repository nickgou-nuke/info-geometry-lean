import InfoGeometry.Quantum.KramersPhaseGlideRepresentation
import InfoGeometry.Topology.KleinAffineOrbitQuotient
import InfoGeometry.Clifford.O55FiveGradeKramersBridge
import InfoGeometry.Clifford.Pin55KramersContactMultigrading

/-! A typed capstone for the Kramers, Klein, and native O(5,5) structures.
The carriers remain separate; no external Pin generator-count artifact is
required. -/

noncomputable section
namespace InfoGeometry.Clifford.Pin55KramersKleinFiveGradeClosure

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Quantum.ComplexKramersAntiunitary
open InfoGeometry.Quantum.KramersPhaseGlideRepresentation
open InfoGeometry.Quantum.FiveGradedKramersModule
open InfoGeometry.Topology.KleinDeckNormalForm
open InfoGeometry.Topology.KleinAffineOrbitQuotient
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Clifford.O55FiveGradeKramersBridge
open InfoGeometry.Clifford.O55SymmetricBlockGrading
open InfoGeometry.Exceptional.Freudenthal

theorem complex_kramers_phase_packet
    {z : ℂ} (hunit : star z * z = 1)
    (v : InfoGeometry.Quantum.ComplexKramersAntiunitary.H2) :
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

theorem klein_quotient_readout_packet :
    b * a * b⁻¹ = a⁻¹ ∧
      (∀ g p, InfoGeometry.Topology.KleinDeckNormalForm.deckAct g p = p ↔ g = 1) ∧
      Function.Surjective abelianReadout ∧
      (2 : ℕ) • abelianReadout a = 0 ∧
      Function.Surjective quotientMap ∧
      Topology.IsQuotientMap quotientMap ∧
      (∀ g p, quotientMap
          (InfoGeometry.Topology.KleinAffineOrbitQuotient.deckAct g p) =
        quotientMap p) := by
  exact ⟨klein_conjugation_relation,
    InfoGeometry.Topology.KleinDeckNormalForm.deckAct_eq_self_iff,
    abelianReadout_surjective, horizontal_class_order_two,
    quotientMap_surjective, quotientMap_isQuotient,
    InfoGeometry.Topology.KleinAffineOrbitQuotient.quotientMap_deckAct⟩

theorem o55_kramers_grade_packet
    (g : ConformalGrade) (x : Alg 5)
    (hx : x ∈ gradeSpace g)
    (v : InfoGeometry.Quantum.ComplexKramersAntiunitary.H2) :
    thetaOp x ∈ gradeSpace g.swap ∧
      HasGrade (-toInt g) (kramers (includeConformalGrade g v)) ∧
      o55FiveParity g.swap = o55FiveParity g ∧
      kramers (kramers (includeConformalGrade g v)) =
        -includeConformalGrade g v := by
  exact ⟨theta_maps g x hx,
    (kramers_o55_grade_parity_packet g v).1,
    (kramers_o55_grade_parity_packet g v).2.1,
    (kramers_o55_grade_parity_packet g v).2.2⟩

theorem o55_symmetric_pair_packet :
    splitMetric * splitMetric = (1 : Mat55) ∧
      (∀ X Y, IsO55Even X → IsO55Even Y →
        IsO55Even (commutator X Y)) ∧
      (∀ X Y, IsO55Even X → IsO55Odd Y →
        IsO55Odd (commutator X Y)) ∧
      (∀ X Y, IsO55Odd X → IsO55Odd Y →
        IsO55Even (commutator X Y)) := by
  exact ⟨splitMetric_sq,
    fun _ _ hX hY => o55_even_even hX hY,
    fun _ _ hX hY => o55_even_odd hX hY,
    fun _ _ hX hY => o55_odd_odd hX hY⟩

end InfoGeometry.Clifford.Pin55KramersKleinFiveGradeClosure
end noncomputable section
