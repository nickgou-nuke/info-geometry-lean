import InfoGeometry.CliffordWeyl.ChiralIdeals
import InfoGeometry.Clifford.DiracPauliGamma

noncomputable section

namespace InfoGeometry.CliffordWeyl.Tests

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Clifford.DiracPauliGamma

def diracChirality : ChiralInvolution DiracMatrix :=
  ⟨gamma5, gamma5_mul_self⟩

theorem gamma_odd (index : Fin 4) :
    gamma index * diracChirality.chi = -(diracChirality.chi * gamma index) := by
  apply add_eq_zero_iff_eq_neg.mp
  simpa only [diracChirality, add_comm] using gamma5_anticomm index

example : diracChirality.Pleft * diracChirality.Pleft = diracChirality.Pleft :=
  diracChirality.Pleft_idem

example : diracChirality.Pright * diracChirality.Pright = diracChirality.Pright :=
  diracChirality.Pright_idem

example : diracChirality.Pleft * diracChirality.Pright = 0 :=
  diracChirality.Pleft_mul_Pright

example : diracChirality.Pright * diracChirality.Pleft = 0 :=
  diracChirality.Pright_mul_Pleft

example (index : Fin 4) :
    diracChirality.Pleft * gamma index * diracChirality.Pleft = 0 ∧
      diracChirality.Pright * gamma index * diracChirality.Pright = 0 :=
  diagonal_corners_zero diracChirality (gamma index) (gamma_odd index)

theorem dirac_bivector_even (first second : Fin 4) :
    Commute diracChirality.chi (gamma first * gamma second) :=
  product_commutes_of_anticommutes diracChirality (gamma first) (gamma second)
    (gamma_odd first) (gamma_odd second)

example :
    diracChirality.Pleft * (gamma 1 * gamma 2) * diracChirality.Pright = 0 ∧
      diracChirality.Pright * (gamma 1 * gamma 2) * diracChirality.Pleft = 0 :=
  cross_corners_zero diracChirality _ (dirac_bivector_even 1 2)

theorem gamma0_nonzero : gamma0 ≠ 0 := by
  intro vanishes
  have impossible : (0 : DiracMatrix) = 1 := by
    simpa only [vanishes, zero_mul] using gamma0_mul_self
  exact zero_ne_one impossible

def trivialChirality : ChiralInvolution (ℝ × ℝ) :=
  ⟨1, one_mul 1⟩

example : trivialChirality.Pright = 0 := by
  simp [trivialChirality, ChiralInvolution.Pright]

example : ∃ part : ℝ × ℝ, part * part = part ∧ part ≠ 0 ∧ part ≠ 1 ∧
    part * trivialChirality.Pleft = part := by
  refine ⟨(1, 0), ?_⟩
  norm_num [trivialChirality, ChiralInvolution.Pleft, Prod.mk_mul_mk]

#print axioms complement_Pleft_eq_Pright
#print axioms commute_Pleft
#print axioms commute_Pright
#print axioms Pleft_mul_swap
#print axioms Pright_mul_swap
#print axioms anticommutes_iff_swaps
#print axioms diagonal_corners_zero
#print axioms anticommutes_iff_diagonal_corners_zero
#print axioms off_diagonal_decomposition
#print axioms cross_corners_zero
#print axioms diagonal_decomposition
#print axioms product_commutes_of_anticommutes
#print axioms left_multiplication_swaps_right_ideal
#print axioms right_multiplication_swaps_left_ideal
#print axioms gamma_odd
#print axioms dirac_bivector_even
#print axioms gamma0_nonzero

end InfoGeometry.CliffordWeyl.Tests
