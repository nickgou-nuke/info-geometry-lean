import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution
import InfoGeometry.QuantumContext.MassAsCommutantCoupling
import InfoGeometry.Algebra.IdempotentCornerCommutant

noncomputable section

namespace InfoGeometry.CliffordWeyl

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling
open InfoGeometry.Algebra.IdempotentCornerCommutant

variable {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]
variable (chirality : ChiralInvolution Carrier)

theorem complement_Pleft_eq_Pright :
    complementIdempotent chirality.Pleft = chirality.Pright := by
  unfold complementIdempotent
  rw [← chirality.Pleft_add_Pright]
  abel

theorem commute_Pleft (operator : Carrier) (commutes : Commute chirality.chi operator) :
    Commute chirality.Pleft operator := by
  change chirality.Pleft * operator = operator * chirality.Pleft
  simp only [ChiralInvolution.Pleft, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_add, one_mul, mul_one, commutes.eq]

theorem commute_Pright (operator : Carrier) (commutes : Commute chirality.chi operator) :
    Commute chirality.Pright operator := by
  change chirality.Pright * operator = operator * chirality.Pright
  simp only [ChiralInvolution.Pright, smul_mul_assoc, mul_smul_comm,
    sub_mul, mul_sub, one_mul, mul_one, commutes.eq]

theorem Pleft_mul_swap (operator : Carrier)
    (anticommutes : operator * chirality.chi = -(chirality.chi * operator)) :
    chirality.Pleft * operator = operator * chirality.Pright := by
  simp only [ChiralInvolution.Pleft, ChiralInvolution.Pright,
    smul_mul_assoc, mul_smul_comm, add_mul, mul_sub, one_mul, mul_one,
    anticommutes, sub_neg_eq_add]

theorem Pright_mul_swap (operator : Carrier)
    (anticommutes : operator * chirality.chi = -(chirality.chi * operator)) :
    chirality.Pright * operator = operator * chirality.Pleft := by
  have swap : chirality.Pleft * operator =
      operator * complementIdempotent chirality.Pleft := by
    rw [complement_Pleft_eq_Pright]
    exact Pleft_mul_swap chirality operator anticommutes
  simpa only [complement_Pleft_eq_Pright] using
    swap_complement chirality.Pleft operator swap

theorem anticommutes_iff_swaps (operator : Carrier) :
    operator * chirality.chi = -(chirality.chi * operator) ↔
      chirality.Pleft * operator = operator * chirality.Pright := by
  constructor
  · exact Pleft_mul_swap chirality operator
  · intro swap
    have swap' : chirality.Pleft * operator =
        operator * complementIdempotent chirality.Pleft := by
      simpa only [complement_Pleft_eq_Pright] using swap
    have relation := grading_anticommutes chirality.Pleft operator swap'
    have grading_eq : grading chirality.Pleft = chirality.chi := by
      rw [grading, complement_Pleft_eq_Pright, chirality.Pleft_sub_Pright]
    rw [grading_eq] at relation
    have reversed : operator * chirality.chi + chirality.chi * operator = 0 := by
      simpa only [add_comm] using relation
    exact add_eq_zero_iff_eq_neg.mp reversed

theorem diagonal_corners_zero (operator : Carrier)
    (anticommutes : operator * chirality.chi = -(chirality.chi * operator)) :
    chirality.Pleft * operator * chirality.Pleft = 0 ∧
      chirality.Pright * operator * chirality.Pright = 0 := by
  have swap : chirality.Pleft * operator =
      operator * complementIdempotent chirality.Pleft := by
    rw [complement_Pleft_eq_Pright]
    exact Pleft_mul_swap chirality operator anticommutes
  have idempotent : IsIdempotentElem chirality.Pleft := chirality.Pleft_idem
  constructor
  · exact diagonal_corner_zero chirality.Pleft operator idempotent swap
  · simpa only [complement_Pleft_eq_Pright] using
      complement_corner_zero chirality.Pleft operator idempotent swap

theorem anticommutes_iff_diagonal_corners_zero (operator : Carrier) :
    operator * chirality.chi = -(chirality.chi * operator) ↔
      chirality.Pleft * operator * chirality.Pleft = 0 ∧
        chirality.Pright * operator * chirality.Pright = 0 := by
  constructor
  · exact diagonal_corners_zero chirality operator
  · rintro ⟨left_zero, right_zero⟩
    apply (anticommutes_iff_swaps chirality operator).mpr
    calc
      chirality.Pleft * operator =
          chirality.Pleft * operator * (chirality.Pleft + chirality.Pright) := by
        rw [chirality.Pleft_add_Pright, mul_one]
      _ = chirality.Pleft * operator * chirality.Pright := by
        rw [mul_add, left_zero, zero_add]
      _ = (chirality.Pleft + chirality.Pright) * operator * chirality.Pright := by
        rw [add_mul, add_mul, right_zero, add_zero]
      _ = operator * chirality.Pright := by
        rw [chirality.Pleft_add_Pright, one_mul]

theorem off_diagonal_decomposition (operator : Carrier)
    (anticommutes : operator * chirality.chi = -(chirality.chi * operator)) :
    operator = chirality.Pleft * operator * chirality.Pright +
      chirality.Pright * operator * chirality.Pleft := by
  obtain ⟨left_zero, right_zero⟩ := diagonal_corners_zero chirality operator anticommutes
  simpa only [component11, component10, component01, component00,
    complement_Pleft_eq_Pright, left_zero, right_zero, zero_add, add_zero] using
    peirce_decomposition chirality.Pleft operator

theorem cross_corners_zero (operator : Carrier) (commutes : Commute chirality.chi operator) :
    chirality.Pleft * operator * chirality.Pright = 0 ∧
      chirality.Pright * operator * chirality.Pleft = 0 := by
  constructor
  · rw [(commute_Pleft chirality operator commutes).eq, mul_assoc,
      chirality.Pleft_mul_Pright, mul_zero]
  · rw [(commute_Pright chirality operator commutes).eq, mul_assoc,
      chirality.Pright_mul_Pleft, mul_zero]

theorem diagonal_decomposition (operator : Carrier) (commutes : Commute chirality.chi operator) :
    operator = chirality.Pleft * operator * chirality.Pleft +
      chirality.Pright * operator * chirality.Pright := by
  obtain ⟨left_zero, right_zero⟩ := cross_corners_zero chirality operator commutes
  simpa only [component11, component10, component01, component00,
    complement_Pleft_eq_Pright, left_zero, right_zero, add_zero] using
    peirce_decomposition chirality.Pleft operator

theorem product_commutes_of_anticommutes (left right : Carrier)
    (left_odd : left * chirality.chi = -(chirality.chi * left))
    (right_odd : right * chirality.chi = -(chirality.chi * right)) :
    Commute chirality.chi (left * right) := by
  have reverse_left : chirality.chi * left = -(left * chirality.chi) := by
    rw [left_odd, neg_neg]
  have reverse_right : chirality.chi * right = -(right * chirality.chi) := by
    rw [right_odd, neg_neg]
  change chirality.chi * (left * right) = (left * right) * chirality.chi
  calc
    chirality.chi * (left * right) = (chirality.chi * left) * right := by
      rw [mul_assoc]
    _ = -(left * (chirality.chi * right)) := by
      rw [reverse_left, neg_mul, mul_assoc]
    _ = left * (right * chirality.chi) := by
      rw [reverse_right, mul_neg, neg_neg]
    _ = (left * right) * chirality.chi := by rw [mul_assoc]

theorem left_multiplication_swaps_right_ideal (operator : Carrier)
    (anticommutes : operator * chirality.chi = -(chirality.chi * operator)) :
    Set.MapsTo (fun vector => operator * vector)
      (principalRightIdeal chirality.Pleft) (principalRightIdeal chirality.Pright) := by
  intro vector member
  change chirality.Pright * (operator * vector) = operator * vector
  change chirality.Pleft * vector = vector at member
  rw [← mul_assoc, Pright_mul_swap chirality operator anticommutes, mul_assoc, member]

theorem right_multiplication_swaps_left_ideal (operator : Carrier)
    (anticommutes : operator * chirality.chi = -(chirality.chi * operator)) :
    Set.MapsTo (fun vector => vector * operator)
      (principalLeftIdeal chirality.Pleft) (principalLeftIdeal chirality.Pright) := by
  intro vector member
  change (vector * operator) * chirality.Pright = vector * operator
  change vector * chirality.Pleft = vector at member
  rw [mul_assoc, ← Pleft_mul_swap chirality operator anticommutes, ← mul_assoc, member]

end InfoGeometry.CliffordWeyl
