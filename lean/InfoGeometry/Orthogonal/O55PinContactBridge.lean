import InfoGeometry.Orthogonal.O55WittNullFrame
import proofs.PinO55GlideReflection

/-!
# Contact grading and the existing `Pin(5,5)` model

The repository already contains a Clifford/Pin realization of a split `(5,5)`
carrier.  This file records exact common readouts—dimension, infinitesimal
count, null-sheet exchange, orientation reversal and contact-grade reversal—
without declaring the two independently constructed representations equal.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

theorem matrix_clifford_count_agreement :
    Fintype.card (Fin 10) = PinO55GlideReflection.o55CarrierDimension ∧
      Nat.choose 10 2 = PinO55GlideReflection.o55GeneratorCount := by
  have hm := carrier_and_generator_counts
  have hc := PinO55GlideReflection.o55_glide_counts
  exact ⟨hm.1.trans hc.1.symm, hm.2.trans hc.2.1.symm⟩

theorem pin_crosscap_n_to_neg_nbar :
    Clifford55.twisted_adj
        PinO55GlideReflection.crosscapReflectionPin55
        (Clifford55.n_pair PinO55GlideReflection.crosscapIndex) =
      -Clifford55.ι55
        (Clifford55.nbar_pair PinO55GlideReflection.crosscapIndex) :=
  PinO55GlideReflection.crosscap_pin_twisted_adj_n_to_neg_nbar

theorem pin_crosscap_nbar_to_neg_n :
    Clifford55.twisted_adj
        PinO55GlideReflection.crosscapReflectionPin55
        (Clifford55.nbar_pair PinO55GlideReflection.crosscapIndex) =
      -Clifford55.ι55
        (Clifford55.n_pair PinO55GlideReflection.crosscapIndex) :=
  PinO55GlideReflection.crosscap_pin_twisted_adj_nbar_to_neg_n

theorem pin_crosscap_orientation_sign :
    PinO55GlideReflection.crosscapOrientationSign = -1 :=
  PinO55GlideReflection.crosscap_orientation_reversing

theorem pin_klein_glide_packet :
    (∀ z : ℂ,
      KleinBottle.G (KleinBottle.T z) =
        KleinBottle.T_inv (KleinBottle.G z)) ∧
      (∀ z : ℂ, KleinBottle.G (KleinBottle.G z) = z + 2) :=
  PinO55GlideReflection.mandatory_glide_relation

/-- Contact-grade reversal in the endomorphism model and null-sheet exchange
in the Clifford model, without an unproved intertwiner. -/
theorem contact_pin_grade_sheet_packet
    {k : ℤ} {A : O55Lie}
    (hA : A ∈ contactGradeSpace k) :
    crosscapConjugation A ∈ contactGradeSpace (-k) ∧
      crosscapConjugation (crosscapConjugation A) = A ∧
      Fintype.card (Fin 10) = PinO55GlideReflection.o55CarrierDimension ∧
      Nat.choose 10 2 = PinO55GlideReflection.o55GeneratorCount ∧
      PinO55GlideReflection.crosscapOrientationSign = -1 ∧
      Clifford55.twisted_adj
          PinO55GlideReflection.crosscapReflectionPin55
          (Clifford55.n_pair PinO55GlideReflection.crosscapIndex) =
        -Clifford55.ι55
          (Clifford55.nbar_pair PinO55GlideReflection.crosscapIndex) ∧
      Clifford55.twisted_adj
          PinO55GlideReflection.crosscapReflectionPin55
          (Clifford55.nbar_pair PinO55GlideReflection.crosscapIndex) =
        -Clifford55.ι55
          (Clifford55.n_pair PinO55GlideReflection.crosscapIndex) := by
  have hsq := LinearMap.congr_fun crosscapConjugation_sq A
  exact ⟨crosscap_reverses_grade hA,
    by simpa [Module.End.mul_apply] using hsq,
    matrix_clifford_count_agreement.1,
    matrix_clifford_count_agreement.2,
    pin_crosscap_orientation_sign,
    pin_crosscap_n_to_neg_nbar,
    pin_crosscap_nbar_to_neg_n⟩

/-- Full contact/Pin/projective-boundary covariance packet. -/
theorem contact_pin_boundary_packet
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket)
    (hf : IsBraWeight b B.bra)
    (hA : A ∈ contactGradeSpace k) :
    IsKetWeight (-a) B.crosscap.ket ∧
      IsBraWeight (-b) B.crosscap.bra ∧
      crosscapConjugation A ∈ contactGradeSpace (-k) ∧
      B.crosscap.readout (crosscapConjugation A : End55) =
        B.readout (A : End55) ∧
      PinO55GlideReflection.crosscapOrientationSign = -1 := by
  rcases crosscap_selection_packet B hv hf hA with
    ⟨hket, hbra, hgrade, hread⟩
  exact ⟨hket, hbra, hgrade, hread, pin_crosscap_orientation_sign⟩

end InfoGeometry.Orthogonal.O55Contact
