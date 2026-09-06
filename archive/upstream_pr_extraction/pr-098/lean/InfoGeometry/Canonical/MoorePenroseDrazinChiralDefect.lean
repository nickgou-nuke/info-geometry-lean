import InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.DrazinGreen

/-!
# Moore--Penrose versus Drazin projectors for a Cuntz chiral pair

This owner uses the repository's actual `CuntzTwoIsometry` carrier.  For
`Q₊ = S₁ S₂†` and `Q₋ = S₂ S₁†`, the Cuntz relations give a genuine
Moore--Penrose pair, while nilpotence gives the zero Drazin core projector at
index two.  The resulting projector difference is the Peirce/chiral
operator.  Here `Drazin_Projector` means the active core projector `A * Aᴰ`;
the complementary Drazin residue is `1 - A * Aᴰ`.  The chiral operator is
not identified with a spin generator or a topological invariant in this
owner.  No anomaly or nonassociative claim is made here: the carrier is a
ring, so its ordinary associator vanishes by associativity.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.MoorePenroseDrazinChiralDefect

open InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin

variable {K A : Type*}
variable [CommRing K] [Ring A] [Algebra K A] [StarRing A]

def qPlus (ck : CuntzTwoIsometry K A) : A :=
  ck.S1 * star ck.S2

def qMinus (ck : CuntzTwoIsometry K A) : A :=
  ck.S2 * star ck.S1

def ePlus (ck : CuntzTwoIsometry K A) : A :=
  ck.S1 * star ck.S1

def eMinus (ck : CuntzTwoIsometry K A) : A :=
  ck.S2 * star ck.S2

def chiralParity (ck : CuntzTwoIsometry K A) : A :=
  ePlus ck - eMinus ck

theorem qPlus_sq (ck : CuntzTwoIsometry K A) :
    qPlus ck * qPlus ck = 0 := by
  unfold qPlus
  calc
    (ck.S1 * star ck.S2) * (ck.S1 * star ck.S2) =
        ck.S1 * (star ck.S2 * ck.S1) * star ck.S2 := by
          noncomm_ring
    _ = 0 := by rw [ck.S2_star_S1, mul_zero, zero_mul]

theorem qMinus_sq (ck : CuntzTwoIsometry K A) :
    qMinus ck * qMinus ck = 0 := by
  unfold qMinus
  calc
    (ck.S2 * star ck.S1) * (ck.S2 * star ck.S1) =
        ck.S2 * (star ck.S1 * ck.S2) * star ck.S1 := by
          noncomm_ring
    _ = 0 := by rw [ck.S1_star_S2, mul_zero, zero_mul]

theorem qPlus_mul_qMinus (ck : CuntzTwoIsometry K A) :
    qPlus ck * qMinus ck = ePlus ck := by
  unfold qPlus qMinus ePlus
  calc
    (ck.S1 * star ck.S2) * (ck.S2 * star ck.S1) =
        ck.S1 * (star ck.S2 * ck.S2) * star ck.S1 := by
          noncomm_ring
    _ = ck.S1 * star ck.S1 := by rw [ck.S2_star_S2, mul_one]

theorem qMinus_mul_qPlus (ck : CuntzTwoIsometry K A) :
    qMinus ck * qPlus ck = eMinus ck := by
  unfold qMinus qPlus eMinus
  calc
    (ck.S2 * star ck.S1) * (ck.S1 * star ck.S2) =
        ck.S2 * (star ck.S1 * ck.S1) * star ck.S2 := by
          noncomm_ring
    _ = ck.S2 * star ck.S2 := by rw [ck.S1_star_S1, mul_one]

theorem qPlus_star_mul_qPlus (ck : CuntzTwoIsometry K A) :
    star (qPlus ck) * qPlus ck = eMinus ck := by
  unfold qPlus eMinus
  rw [star_mul, star_star]
  calc
    (ck.S2 * star ck.S1) * (ck.S1 * star ck.S2) =
        ck.S2 * (star ck.S1 * ck.S1) * star ck.S2 := by noncomm_ring
    _ = ck.S2 * star ck.S2 := by rw [ck.S1_star_S1, mul_one]

theorem qMinus_star_mul_qMinus (ck : CuntzTwoIsometry K A) :
    star (qMinus ck) * qMinus ck = ePlus ck := by
  unfold qMinus ePlus
  rw [star_mul, star_star]
  calc
    (ck.S1 * star ck.S2) * (ck.S2 * star ck.S1) =
        ck.S1 * (star ck.S2 * ck.S2) * star ck.S1 := by noncomm_ring
    _ = ck.S1 * star ck.S1 := by rw [ck.S2_star_S2, mul_one]

theorem qPlus_star_eq_qMinus (ck : CuntzTwoIsometry K A) :
    star (qPlus ck) = qMinus ck := by
  simp [qPlus, qMinus, star_mul]

theorem qMinus_star_eq_qPlus (ck : CuntzTwoIsometry K A) :
    star (qMinus ck) = qPlus ck := by
  simp [qPlus, qMinus, star_mul]

theorem qPlus_moorePenrose (ck : CuntzTwoIsometry K A) :
    IsMoorePenroseInverse (qPlus ck) (qMinus ck) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · calc
      qPlus ck * qMinus ck * qPlus ck =
          (qPlus ck * qMinus ck) * qPlus ck := by rw [mul_assoc]
      _ = ePlus ck * qPlus ck := by rw [qPlus_mul_qMinus]
      _ = qPlus ck := by
        unfold ePlus qPlus
        calc
          (ck.S1 * star ck.S1) * (ck.S1 * star ck.S2) =
              ck.S1 * (star ck.S1 * ck.S1) * star ck.S2 := by
                noncomm_ring
          _ = qPlus ck := by rw [ck.S1_star_S1, mul_one]; rfl
  · calc
      qMinus ck * qPlus ck * qMinus ck =
          (qMinus ck * qPlus ck) * qMinus ck := by rw [mul_assoc]
      _ = eMinus ck * qMinus ck := by rw [qMinus_mul_qPlus]
      _ = qMinus ck := by
        unfold eMinus qMinus
        calc
          (ck.S2 * star ck.S2) * (ck.S2 * star ck.S1) =
              ck.S2 * (star ck.S2 * ck.S2) * star ck.S1 := by
                noncomm_ring
          _ = qMinus ck := by rw [ck.S2_star_S2, mul_one]; rfl
  · rw [qPlus_mul_qMinus]
    unfold ePlus
    simp [star_mul]
  · rw [qMinus_mul_qPlus]
    unfold eMinus
    simp [star_mul]

theorem qMinus_moorePenrose (ck : CuntzTwoIsometry K A) :
    IsMoorePenroseInverse (qMinus ck) (qPlus ck) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · calc
      qMinus ck * qPlus ck * qMinus ck =
          (qMinus ck * qPlus ck) * qMinus ck := by rw [mul_assoc]
      _ = eMinus ck * qMinus ck := by rw [qMinus_mul_qPlus]
      _ = qMinus ck := by
        unfold eMinus qMinus
        calc
          (ck.S2 * star ck.S2) * (ck.S2 * star ck.S1) =
              ck.S2 * (star ck.S2 * ck.S2) * star ck.S1 := by
                noncomm_ring
          _ = qMinus ck := by rw [ck.S2_star_S2, mul_one]; rfl
  · calc
      qPlus ck * qMinus ck * qPlus ck =
          (qPlus ck * qMinus ck) * qPlus ck := by rw [mul_assoc]
      _ = ePlus ck * qPlus ck := by rw [qPlus_mul_qMinus]
      _ = qPlus ck := by
        unfold ePlus qPlus
        calc
          (ck.S1 * star ck.S1) * (ck.S1 * star ck.S2) =
              ck.S1 * (star ck.S1 * ck.S1) * star ck.S2 := by
                noncomm_ring
          _ = qPlus ck := by rw [ck.S1_star_S1, mul_one]; rfl
  · rw [qMinus_mul_qPlus]
    unfold eMinus
    simp [star_mul]
  · rw [qPlus_mul_qMinus]
    unfold ePlus
    simp [star_mul]

theorem moorePenroseProjector_plus_eq_ePlus (ck : CuntzTwoIsometry K A) :
    MP_Projector (qPlus ck) (qMinus ck) (qPlus_moorePenrose ck) = ePlus ck := by
  exact qPlus_mul_qMinus ck

theorem moorePenroseProjector_minus_eq_eMinus (ck : CuntzTwoIsometry K A) :
    MP_Projector (qMinus ck) (qPlus ck) (qMinus_moorePenrose ck) = eMinus ck := by
  exact qMinus_mul_qPlus ck

theorem qPlus_penrose_one (ck : CuntzTwoIsometry K A) :
    qPlus ck * star (qPlus ck) * qPlus ck = qPlus ck := by
  rw [qPlus_star_eq_qMinus]
  exact (qPlus_moorePenrose ck).aba_eq_a

theorem qPlus_penrose_two (ck : CuntzTwoIsometry K A) :
    star (qPlus ck) * qPlus ck * star (qPlus ck) = star (qPlus ck) := by
  rw [qPlus_star_eq_qMinus]
  exact (qPlus_moorePenrose ck).bab_eq_b

theorem qMinus_penrose_one (ck : CuntzTwoIsometry K A) :
    qMinus ck * star (qMinus ck) * qMinus ck = qMinus ck := by
  rw [qMinus_star_eq_qPlus]
  exact (qMinus_moorePenrose ck).aba_eq_a

theorem qMinus_penrose_two (ck : CuntzTwoIsometry K A) :
    star (qMinus ck) * qMinus ck * star (qMinus ck) = star (qMinus ck) := by
  rw [qMinus_star_eq_qPlus]
  exact (qMinus_moorePenrose ck).bab_eq_b

theorem qPlus_drazin_zero (ck : CuntzTwoIsometry K A) :
    IsDrazinInverse (qPlus ck) 0 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simp
  · simp
  · rw [show qPlus ck ^ 2 = 0 by simpa [pow_two] using qPlus_sq ck]
    simp

theorem qMinus_drazin_zero (ck : CuntzTwoIsometry K A) :
    IsDrazinInverse (qMinus ck) 0 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simp
  · simp
  · rw [show qMinus ck ^ 2 = 0 by simpa [pow_two] using qMinus_sq ck]
    simp

theorem drazinProjector_plus_eq_zero (ck : CuntzTwoIsometry K A) :
    Drazin_Projector (qPlus ck) 0 2 (qPlus_drazin_zero ck) = 0 := by
  simp [Drazin_Projector]

theorem drazinProjector_minus_eq_zero (ck : CuntzTwoIsometry K A) :
    Drazin_Projector (qMinus ck) 0 2 (qMinus_drazin_zero ck) = 0 := by
  simp [Drazin_Projector]

theorem drazinResidueProjector_plus_eq_one (ck : CuntzTwoIsometry K A) :
    Drazin_ResidueProjector (qPlus ck) 0 2 (qPlus_drazin_zero ck) = 1 := by
  simp [Drazin_ResidueProjector, Drazin_Projector]

theorem drazinResidueProjector_minus_eq_one (ck : CuntzTwoIsometry K A) :
    Drazin_ResidueProjector (qMinus ck) 0 2 (qMinus_drazin_zero ck) = 1 := by
  simp [Drazin_ResidueProjector, Drazin_Projector]

theorem moorePenrose_defect_eq_chiralParity (ck : CuntzTwoIsometry K A) :
    MP_Projector (qPlus ck) (qMinus ck) (qPlus_moorePenrose ck) -
        MP_Projector (qMinus ck) (qPlus ck) (qMinus_moorePenrose ck) =
      chiralParity ck := by
  rw [moorePenroseProjector_plus_eq_ePlus,
    moorePenroseProjector_minus_eq_eMinus]
  rfl

theorem moorePenrose_sum_eq_one
    (ck : CuntzTwoIsometry K A)
    (hcomplete : ePlus ck + eMinus ck = 1) :
    MP_Projector (qPlus ck) (qMinus ck) (qPlus_moorePenrose ck) +
        MP_Projector (qMinus ck) (qPlus ck) (qMinus_moorePenrose ck) = 1 := by
  rw [moorePenroseProjector_plus_eq_ePlus,
    moorePenroseProjector_minus_eq_eMinus]
  exact hcomplete

theorem chiralParity_sq_one
    (ck : CuntzTwoIsometry K A)
    (hcomplete : ePlus ck + eMinus ck = 1) :
    chiralParity ck * chiralParity ck = 1 := by
  unfold chiralParity ePlus eMinus
  have h11 : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) =
      ck.S1 * star ck.S1 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1,
      ck.S1_star_S1, mul_one]
  have h22 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) =
      ck.S2 * star ck.S2 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2,
      ck.S2_star_S2, mul_one]
  have h12 : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2,
      ck.S1_star_S2, mul_zero, zero_mul]
  have h21 : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1,
      ck.S2_star_S1, mul_zero, zero_mul]
  calc
    (ck.S1 * star ck.S1 - ck.S2 * star ck.S2) *
        (ck.S1 * star ck.S1 - ck.S2 * star ck.S2) =
        ck.S1 * star ck.S1 + ck.S2 * star ck.S2 := by
          noncomm_ring [h11, h22, h12, h21]
    _ = 1 := hcomplete

theorem drazin_moorePenrose_defect_eq_chiralParity (ck : CuntzTwoIsometry K A) :
    (MP_Projector (qPlus ck) (qMinus ck) (qPlus_moorePenrose ck) -
        Drazin_Projector (qPlus ck) 0 2 (qPlus_drazin_zero ck)) -
      (MP_Projector (qMinus ck) (qPlus ck) (qMinus_moorePenrose ck) -
        Drazin_Projector (qMinus ck) 0 2 (qMinus_drazin_zero ck)) =
      chiralParity ck := by
  rw [drazinProjector_plus_eq_zero, drazinProjector_minus_eq_zero]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    moorePenrose_defect_eq_chiralParity ck

omit [StarRing A] in
theorem associator_eq_zero (X Y Z : A) :
    (X * Y) * Z - X * (Y * Z) = 0 := by
  rw [mul_assoc]
  simp

end InfoGeometry.Canonical.MoorePenroseDrazinChiralDefect
