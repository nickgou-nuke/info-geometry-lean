import InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

namespace InfoGeometry.Algebra.Zorn.G2PeircePrefixCarrierFacts

open _root_.InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints
open InfoGeometry.Algebra.Zorn.G2PeirceFibration
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

noncomputable instance admissibleBasis7Carrier_fintype :
    Fintype AdmissibleBasis7Carrier :=
  Fintype.ofEquiv SplitOctF2Aut admissibleBasis7Equiv

noncomputable instance nonzeroSquareZero_finite :
    Finite NonzeroSquareZero :=
  Finite.of_injective (fun x : NonzeroSquareZero => x.1)
    (fun _ _ h => Subtype.ext h)

noncomputable instance nonzeroSquareZero_fintype :
    Fintype NonzeroSquareZero :=
  Fintype.ofFinite _

noncomputable instance peircePlusFiber_finite
    (p : NontrivialIdempotent) : Finite (PeircePlusFiber p) :=
  Finite.of_injective (fun x : PeircePlusFiber p => x.1)
    (fun _ _ h => Subtype.ext h)

noncomputable instance peircePlusFiber_fintype
    (p : NontrivialIdempotent) : Fintype (PeircePlusFiber p) :=
  Fintype.ofFinite _

def AdmissibleFirstPrefix : Type :=
  {p : NontrivialIdempotent // ∃ v : AdmissibleBasis7Carrier,
    admissibleBasis7_first_prefix_code v = p}

def occurringFirstPrefix
    (v : AdmissibleBasis7Carrier) : AdmissibleFirstPrefix :=
  ⟨admissibleBasis7_first_prefix_code v, ⟨v, rfl⟩⟩

noncomputable instance occurringFirstPrefix_finite :
    Finite AdmissibleFirstPrefix :=
  Finite.of_injective (fun p : AdmissibleFirstPrefix => p.1)
    Subtype.val_injective

noncomputable instance occurringFirstPrefix_fintype :
    Fintype AdmissibleFirstPrefix :=
  Fintype.ofFinite _

theorem nontrivialIdempotent_card_eq_72 :
    Fintype.card NontrivialIdempotent = 72 := by
  native_decide

theorem occurringFirstPrefix_card_le_72 :
    Fintype.card AdmissibleFirstPrefix ≤ 72 := by
  have h := Fintype.card_le_of_injective
    (fun p : AdmissibleFirstPrefix => p.1)
    Subtype.val_injective
  rw [nontrivialIdempotent_card_eq_72] at h
  exact h

theorem no_injective_nontrivialIdempotent_to_octImIsotropicPoint :
    ¬ ∃ f : NontrivialIdempotent → OctImIsotropicPoint,
      Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  rw [nontrivialIdempotent_card_eq_72, octImIsotropicPoint_card] at hcard
  omega

def AdmissibleSecondPrefix
    (p : NontrivialIdempotent) : Type :=
  {x : PeircePlusFiber p // Nonempty (ResidualFiber p x)}

noncomputable instance admissibleSecondPrefix_finite
    (p : NontrivialIdempotent) : Finite (AdmissibleSecondPrefix p) :=
  Finite.of_injective (fun x : AdmissibleSecondPrefix p => x.1)
    (fun _ _ h => Subtype.ext h)

noncomputable instance admissibleSecondPrefix_fintype
    (p : NontrivialIdempotent) : Fintype (AdmissibleSecondPrefix p) :=
  Fintype.ofFinite _

def occurringSecondPrefix
    (v : AdmissibleBasis7Carrier) :
    AdmissibleSecondPrefix (admissibleBasis7_first_prefix_code v) :=
  ⟨admissibleBasis7Second v,
    ⟨⟨v, ⟨rfl, rfl⟩⟩⟩⟩

theorem occurringFirstPrefix_value
    (v : AdmissibleBasis7Carrier) :
    (occurringFirstPrefix v).1 =
      admissibleBasis7_first_prefix_code v :=
  rfl

theorem occurringSecondPrefix_value
    (v : AdmissibleBasis7Carrier) :
    (occurringSecondPrefix v).1 =
      admissibleBasis7Second v :=
  rfl

theorem occurringSecondPrefix_card_le_peircePlusFiber
    (p : NontrivialIdempotent) :
    Fintype.card (AdmissibleSecondPrefix p) ≤
      Fintype.card (PeircePlusFiber p) := by
  exact Fintype.card_le_of_injective
    (fun x : AdmissibleSecondPrefix p => x.1)
    (fun _ _ h => Subtype.ext h)

def occurringPeirceCode
    (v : AdmissibleBasis7Carrier) :
    Σ p : AdmissibleFirstPrefix,
      Σ x : AdmissibleSecondPrefix p.1,
        ResidualFiber p.1 x.1 := by
  let p := occurringFirstPrefix v
  let x : AdmissibleSecondPrefix p.1 :=
    ⟨admissibleBasis7Second v,
      ⟨⟨v, ⟨rfl, rfl⟩⟩⟩⟩
  exact ⟨p, x, ⟨v, ⟨rfl, rfl⟩⟩⟩

theorem occurringPeirceCode_injective :
    Function.Injective occurringPeirceCode := by
  intro v w h
  exact congrArg (fun z => z.2.2.1) h

theorem admissibleBasis7_card_le_occurringPeirceSigma :
    Fintype.card AdmissibleBasis7Carrier ≤
      Fintype.card
        (Σ p : AdmissibleFirstPrefix,
          Σ x : AdmissibleSecondPrefix p.1,
            ResidualFiber p.1 x.1) := by
  exact Fintype.card_le_of_injective
    occurringPeirceCode occurringPeirceCode_injective

end InfoGeometry.Algebra.Zorn.G2PeircePrefixCarrierFacts
