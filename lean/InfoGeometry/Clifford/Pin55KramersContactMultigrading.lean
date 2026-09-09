import InfoGeometry.Quantum.FiveGradedKramersModule
import InfoGeometry.Topology.KleinParityDeck
import InfoGeometry.Exceptional.FreudenthalContactParityGrading
import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading
import InfoGeometry.Clifford.O55SymmetricBlockGrading

/-! Native product grading for the independent Kramers, symmetric-pair, and
Klein orientation labels.  The unavailable external Pin generator-count
surface is deliberately not imported or replaced by an assumed representation.
-/

noncomputable section
namespace InfoGeometry.Clifford.Pin55KramersContactMultigrading

open InfoGeometry.Quantum.FiveGradedKramersModule
open InfoGeometry.Topology.KleinParityDeck
open InfoGeometry.Exceptional.Freudenthal

@[ext] structure MultiDegree where
  contactWeight : ℤ
  contactParity : ZMod 2
  o55Parity : ZMod 2
  orientationParity : ZMod 2
  deriving DecidableEq, Repr

def deckOrientationParity (g : Deck) : ZMod 2 := g.parity

@[simp] theorem deckOrientationParity_a : deckOrientationParity generatorA = 0 := by
  rfl

@[simp] theorem deckOrientationParity_b : deckOrientationParity generatorB = 1 := by
  rfl

def degreeOf (w : Weight) (q : ZMod 2) (g : Deck) : MultiDegree where
  contactWeight := w.value
  contactParity := w.parity
  o55Parity := q
  orientationParity := deckOrientationParity g

def kramersOppositeDegree (d : MultiDegree) : MultiDegree where
  contactWeight := -d.contactWeight
  contactParity := d.contactParity
  o55Parity := d.o55Parity
  orientationParity := d.orientationParity

@[simp] theorem kramersOppositeDegree_involutive (d : MultiDegree) :
    kramersOppositeDegree (kramersOppositeDegree d) = d := by
  ext <;> simp [kramersOppositeDegree]

@[simp] theorem degreeOf_opposite (w : Weight) (q : ZMod 2) (g : Deck) :
    degreeOf w.opposite q g = kramersOppositeDegree (degreeOf w q g) := by
  ext <;> simp [degreeOf, kramersOppositeDegree]

theorem contact_multigrade_bracket
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) {k l : ℤ}
    {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l :=
  symplecticContact_lie_mem_multigrade D hu hv

theorem kramers_contact_packet
    (w : Weight)
    (v : InfoGeometry.Quantum.ComplexKramersAntiunitary.H2) :
    HasGrade w.value (fibreInclude w v) ∧
      HasGrade (-w.value) (kramers (fibreInclude w v)) ∧
      w.opposite.parity = w.parity ∧
      kramers (kramers (fibreInclude w v)) = -fibreInclude w v := by
  exact ⟨include_hasGrade w v,
    kramers_hasGrade_neg (include_hasGrade w v),
    Weight.parity_opposite w, kramers_sq (fibreInclude w v)⟩

end InfoGeometry.Clifford.Pin55KramersContactMultigrading
end noncomputable section
