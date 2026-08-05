import InfoGeometry.Clifford.Cl55WittPinAction

namespace InfoGeometry.Clifford.Clifford55

open CliffordAlgebra

noncomputable def unitPinTwistedAdj (u : Cl55ˣ) (v : V55) : Cl55 :=
  involute (Q := Q55) (u : Cl55) * ι55 v * (↑u⁻¹ : Cl55)

private theorem fNegUnit_inv (i : Fin 5) :
    (↑(fNegUnit i)⁻¹ : Cl55) = -ι55 (f_neg i) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [fNegUnit_coe]
  calc
    ι55 (f_neg i) * -ι55 (f_neg i) =
        -(ι55 (f_neg i) * ι55 (f_neg i)) := by rw [mul_neg]
    _ = 1 := by rw [f_neg_mul_self]; simp

private theorem negative_pin_reflection_orthogonal {A : Type*} [Ring A]
    (e f : A) (hff : f * f = -1)
    (hanti : f * e + e * f = 0) :
    -f * e * (-f) = e := by
  have hfe : f * e = -(e * f) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hanti
  calc
    -f * e * (-f) = f * e * f := by noncomm_ring
    _ = -(e * f) * f := by rw [hfe]
    _ = -((e * f) * f) := by rw [neg_mul]
    _ = -(e * (f * f)) := by rw [mul_assoc]
    _ = e := by rw [hff]; simp

theorem fNegUnit_twisted_e_pos (i : Fin 5) :
    unitPinTwistedAdj (fNegUnit i) (e_pos i) = ι55 (e_pos i) := by
  rw [unitPinTwistedAdj, fNegUnit_coe, CliffordAlgebra.involute_ι,
    fNegUnit_inv]
  apply negative_pin_reflection_orthogonal
  · exact f_neg_mul_self i
  · have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Q55) (e_pos_ortho_f_neg i i)
    simpa [add_comm] using h

theorem fNegUnit_twisted_f_neg (i : Fin 5) :
    unitPinTwistedAdj (fNegUnit i) (f_neg i) = -ι55 (f_neg i) := by
  rw [unitPinTwistedAdj, fNegUnit_coe, CliffordAlgebra.involute_ι,
    fNegUnit_inv]
  calc
    -ι55 (f_neg i) * ι55 (f_neg i) * -ι55 (f_neg i) =
        (ι55 (f_neg i) * ι55 (f_neg i)) * ι55 (f_neg i) := by
          noncomm_ring
    _ = (-1 : Cl55) * ι55 (f_neg i) := by rw [f_neg_mul_self]
    _ = -ι55 (f_neg i) := by simp

end InfoGeometry.Clifford.Clifford55
