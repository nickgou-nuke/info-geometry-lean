import InfoGeometry.Quantum.FiveGradedKramersModule
import InfoGeometry.Topology.KleinDeckNormalForm
import InfoGeometry.Exceptional.FreudenthalContactParityGrading
import InfoGeometry.Clifford.O55SymmetricBlockGrading
import proofs.PinO55GlideReflection

/-!
# Pin(5,5), Kramers, Klein, and contact multiple grading

Four gradings/involutions coexist in the reconstructed architecture:

1. the contact integer degree `-2,-1,0,1,2`;
2. its derived parity modulo two;
3. the symmetric-pair parity of `o(5,5)` (compact rotations versus mixed
   boosts);
4. the orientation parity of the Klein deck action.

They are assembled as a product degree rather than identified.  The complex
Kramers operator reverses the contact integer degree while preserving its
mod-two parity.  The native Pin(5,5) crosscap separately exchanges the two
projective null directions and the affine Klein generator reverses
orientation.
-/

noncomputable section

namespace InfoGeometry.Clifford.Pin55KramersContactMultigrading

open InfoGeometry.Quantum.FiveGradedKramersModule
open InfoGeometry.Topology.KleinDeckNormalForm
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Clifford.O55SymmetricBlockGrading

/-- Product of the independent grading labels. -/
@[ext]
structure MultiDegree where
  contactWeight : ℤ
  contactParity : ZMod 2
  o55Parity : ZMod 2
  orientationParity : ZMod 2
  deriving DecidableEq, Repr

/-- Orientation parity read from the glide exponent. -/
def deckOrientationParity (g : Deck) : ZMod 2 :=
  (g.vertical : ZMod 2)

@[simp] theorem deckOrientationParity_a :
    deckOrientationParity a = 0 := by
  rfl

@[simp] theorem deckOrientationParity_b :
    deckOrientationParity b = 1 := by
  rfl

/-- Assemble one finite contact weight, one `o(5,5)` generator family, and one
deck normal form into a product degree. -/
def degreeOf
    (w : Weight)
    (q : O55GradedGeneratorBasis.O55GeneratorGrade)
    (g : Deck) : MultiDegree where
  contactWeight := w.value
  contactParity := w.parity
  o55Parity := generatorParity q
  orientationParity := deckOrientationParity g

/-- Kramers opposition acts only on the integer contact degree; its parity is
unchanged. -/
def kramersOppositeDegree (d : MultiDegree) : MultiDegree where
  contactWeight := -d.contactWeight
  contactParity := d.contactParity
  o55Parity := d.o55Parity
  orientationParity := d.orientationParity

@[simp] theorem kramersOppositeDegree_involutive (d : MultiDegree) :
    kramersOppositeDegree (kramersOppositeDegree d) = d := by
  ext <;> simp [kramersOppositeDegree]

@[simp] theorem degreeOf_opposite
    (w : Weight)
    (q : O55GradedGeneratorBasis.O55GeneratorGrade)
    (g : Deck) :
    degreeOf w.opposite q g =
      kramersOppositeDegree (degreeOf w q g) := by
  ext <;> simp [degreeOf, kramersOppositeDegree]

/-- The `o(5,5)` family partition has twenty even and twenty-five odd
    generators. -/
theorem o55_generator_parity_counts :
    fullEvenGeneratorCount = 20 ∧
      fullOddGeneratorCount = 25 ∧
      fullEvenGeneratorCount + fullOddGeneratorCount = 45 := by
  exact ⟨full_even_generator_count_eq,
    full_odd_generator_count_eq,
    full_even_add_odd_eq⟩

/-- The native Pin(5,5) crosscap exchanges the two projective null rays. -/
theorem pin55_crosscap_projective_null_swap :
    InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence.realSplitPinNullAction
        (InfoGeometry.Clifford.Clifford55.fNegRealPin
          PinO55GlideReflection.crosscapIndex)
        (InfoGeometry.Clifford.Clifford55.nPairProjective
          PinO55GlideReflection.crosscapIndex) =
      InfoGeometry.Clifford.Clifford55.nbarPairProjective
        PinO55GlideReflection.crosscapIndex ∧
    InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence.realSplitPinNullAction
        (InfoGeometry.Clifford.Clifford55.fNegRealPin
          PinO55GlideReflection.crosscapIndex)
        (InfoGeometry.Clifford.Clifford55.nbarPairProjective
          PinO55GlideReflection.crosscapIndex) =
      InfoGeometry.Clifford.Clifford55.nPairProjective
        PinO55GlideReflection.crosscapIndex := by
  exact ⟨PinO55GlideReflection.native_crosscap_projective_n_to_nbar,
    PinO55GlideReflection.native_crosscap_projective_nbar_to_n⟩

/-- The Pin/Klein layer supplies orientation reversal and the glide relation,
    but is not identified with the complex antiunitary. -/
theorem pin55_klein_orientation_packet :
    PinO55GlideReflection.crosscapOrientationSign = -1 ∧
      orientationCharacter b = -1 ∧
      b * a * b⁻¹ = a⁻¹ ∧
      PinO55GlideReflection.o55CarrierDimension = 10 ∧
      PinO55GlideReflection.o55GeneratorCount = 45 := by
  exact ⟨PinO55GlideReflection.crosscap_orientation_reversing,
    orientationCharacter_b,
    klein_conjugation_relation,
    TorusKleinO55Bridge.doubled_cartan_carrier_dimension_eq,
    O55GradedGeneratorBasis.full_graded_generator_count_eq⟩

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The contact bracket carries the integer degree and its quotient parity
    simultaneously. -/
theorem contact_multigrade_bracket
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l :=
  symplecticContact_lie_mem_multigrade D hu hv

/-- Full finite multiple-grading packet.  Each conjunct belongs to its own
carrier; no unsupported isomorphism between the carriers is asserted. -/
theorem pin55_kramers_contact_multigrading_packet
    (w : Weight)
    (v : InfoGeometry.Quantum.ComplexKramersAntiunitary.H2) :
    FiveGradedKramersModule.HasGrade w.value
        (FiveGradedKramersModule.include w v) ∧
      FiveGradedKramersModule.HasGrade (-w.value)
        (FiveGradedKramersModule.kramers
          (FiveGradedKramersModule.include w v)) ∧
      w.opposite.parity = w.parity ∧
      FiveGradedKramersModule.kramers
          (FiveGradedKramersModule.kramers
            (FiveGradedKramersModule.include w v)) =
        -FiveGradedKramersModule.include w v ∧
      fullEvenGeneratorCount = 20 ∧
      fullOddGeneratorCount = 25 ∧
      PinO55GlideReflection.crosscapOrientationSign = -1 ∧
      b * a * b⁻¹ = a⁻¹ := by
  exact ⟨FiveGradedKramersModule.include_hasGrade w v,
    FiveGradedKramersModule.kramers_hasGrade_neg
      (FiveGradedKramersModule.include_hasGrade w v),
    Weight.parity_opposite w,
    FiveGradedKramersModule.kramers_sq
      (FiveGradedKramersModule.include w v),
    full_even_generator_count_eq,
    full_odd_generator_count_eq,
    PinO55GlideReflection.crosscap_orientation_reversing,
    klein_conjugation_relation⟩

end InfoGeometry.Clifford.Pin55KramersContactMultigrading
