import InfoGeometry.Clifford.CrawfordDiracBispinorDensities
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.CliffordWeyl.SpinorBilinearSelection

noncomputable section

namespace InfoGeometry.CliffordWeyl.DiracBilinearChannels

open InfoGeometry.Clifford.CrawfordDiracBispinorDensities
open Matrix

def cliffordDegree : DiracBilinearLabel → ℕ
  | .scalar => 0
  | .vector _ => 1
  | .bivector _ => 2
  | .axial _ => 3
  | .pseudoscalar => 4

def indexedChannel (index : Fin 16) : DiracMatrix :=
  diracBilinearMatrix (finToDiracBilinearLabel index)

def channelCoefficient (operator : DiracMatrix) (index : Fin 16) : ℂ :=
  trace ((indexedChannel index).conjTranspose * operator) / 4

set_option maxHeartbeats 2000000 in
theorem indexedChannel_hs_row_0 (j : Fin 16) :
    trace ((indexedChannel (0 : Fin 16)).conjTranspose * indexedChannel j) =
      if (0 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_1 (j : Fin 16) :
    trace ((indexedChannel (1 : Fin 16)).conjTranspose * indexedChannel j) =
      if (1 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_2 (j : Fin 16) :
    trace ((indexedChannel (2 : Fin 16)).conjTranspose * indexedChannel j) =
      if (2 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_3 (j : Fin 16) :
    trace ((indexedChannel (3 : Fin 16)).conjTranspose * indexedChannel j) =
      if (3 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_4 (j : Fin 16) :
    trace ((indexedChannel (4 : Fin 16)).conjTranspose * indexedChannel j) =
      if (4 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_5 (j : Fin 16) :
    trace ((indexedChannel (5 : Fin 16)).conjTranspose * indexedChannel j) =
      if (5 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_6 (j : Fin 16) :
    trace ((indexedChannel (6 : Fin 16)).conjTranspose * indexedChannel j) =
      if (6 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_7 (j : Fin 16) :
    trace ((indexedChannel (7 : Fin 16)).conjTranspose * indexedChannel j) =
      if (7 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_8 (j : Fin 16) :
    trace ((indexedChannel (8 : Fin 16)).conjTranspose * indexedChannel j) =
      if (8 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_9 (j : Fin 16) :
    trace ((indexedChannel (9 : Fin 16)).conjTranspose * indexedChannel j) =
      if (9 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_10 (j : Fin 16) :
    trace ((indexedChannel (10 : Fin 16)).conjTranspose * indexedChannel j) =
      if (10 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_11 (j : Fin 16) :
    trace ((indexedChannel (11 : Fin 16)).conjTranspose * indexedChannel j) =
      if (11 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_12 (j : Fin 16) :
    trace ((indexedChannel (12 : Fin 16)).conjTranspose * indexedChannel j) =
      if (12 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_13 (j : Fin 16) :
    trace ((indexedChannel (13 : Fin 16)).conjTranspose * indexedChannel j) =
      if (13 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_14 (j : Fin 16) :
    trace ((indexedChannel (14 : Fin 16)).conjTranspose * indexedChannel j) =
      if (14 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
private theorem indexedChannel_hs_row_15 (j : Fin 16) :
    trace ((indexedChannel (15 : Fin 16)).conjTranspose * indexedChannel j) =
      if (15 : Fin 16) = j then 4 else 0 := by
  fin_cases j <;> norm_num [indexedChannel, diracBilinearMatrix, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

set_option maxHeartbeats 2000000 in
theorem indexedChannel_hs_orthogonal (i j : Fin 16) :
    trace ((indexedChannel i).conjTranspose * indexedChannel j) =
      if i = j then 4 else 0 := by
  fin_cases i
  · exact indexedChannel_hs_row_0 j
  · exact indexedChannel_hs_row_1 j
  · exact indexedChannel_hs_row_2 j
  · exact indexedChannel_hs_row_3 j
  · exact indexedChannel_hs_row_4 j
  · exact indexedChannel_hs_row_5 j
  · exact indexedChannel_hs_row_6 j
  · exact indexedChannel_hs_row_7 j
  · exact indexedChannel_hs_row_8 j
  · exact indexedChannel_hs_row_9 j
  · exact indexedChannel_hs_row_10 j
  · exact indexedChannel_hs_row_11 j
  · exact indexedChannel_hs_row_12 j
  · exact indexedChannel_hs_row_13 j
  · exact indexedChannel_hs_row_14 j
  · exact indexedChannel_hs_row_15 j

theorem indexedChannel_linearIndependent : LinearIndependent ℂ indexedChannel := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients h i
  have hread := congrArg
    (fun M : DiracMatrix => trace ((indexedChannel i).conjTranspose * M)) h
  change trace ((indexedChannel i).conjTranspose *
      (∑ j : Fin 16, coefficients j • indexedChannel j)) =
    trace ((indexedChannel i).conjTranspose * (0 : DiracMatrix)) at hread
  rw [Matrix.mul_sum, Matrix.trace_sum] at hread
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hread
  simp_rw [indexedChannel_hs_orthogonal] at hread
  have hcollapse :
      (∑ j : Fin 16, coefficients j * (if i = j then (4 : ℂ) else 0)) =
        coefficients i * 4 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [hcollapse] at hread
  have hzero : coefficients i * 4 = 0 := by simpa using hread
  exact (mul_eq_zero.mp hzero).resolve_right (by norm_num)

noncomputable def indexedChannelBasis : Module.Basis (Fin 16) ℂ DiracMatrix :=
  basisOfLinearIndependentOfCardEqFinrank indexedChannel_linearIndependent (by
    simp [DiracMatrix, Module.finrank_matrix])

@[simp] theorem indexedChannelBasis_apply (i : Fin 16) :
    indexedChannelBasis i = indexedChannel i := by
  simp [indexedChannelBasis]

theorem channelCoefficient_eq_basis_repr (operator : DiracMatrix) (i : Fin 16) :
    channelCoefficient operator i = (indexedChannelBasis.repr operator) i := by
  have hexp :
      (∑ j : Fin 16, (indexedChannelBasis.repr operator) j • indexedChannel j) =
        operator := by
    simpa using Module.Basis.sum_repr indexedChannelBasis operator
  have hread := congrArg
    (fun M : DiracMatrix => trace ((indexedChannel i).conjTranspose * M)) hexp
  change trace ((indexedChannel i).conjTranspose *
      (∑ j : Fin 16, (indexedChannelBasis.repr operator) j • indexedChannel j)) =
    trace ((indexedChannel i).conjTranspose * operator) at hread
  rw [Matrix.mul_sum, Matrix.trace_sum] at hread
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hread
  simp_rw [indexedChannel_hs_orthogonal] at hread
  have hcollapse :
      (∑ j : Fin 16,
        (indexedChannelBasis.repr operator) j * (if i = j then (4 : ℂ) else 0)) =
        (indexedChannelBasis.repr operator) i * 4 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [hcollapse] at hread
  dsimp [channelCoefficient]
  calc
    trace ((indexedChannel i).conjTranspose * operator) / 4 =
        ((indexedChannelBasis.repr operator) i * 4) / 4 := by rw [← hread]
    _ = (indexedChannelBasis.repr operator) i := by ring

theorem channel_reconstruction (operator : DiracMatrix) :
    ∑ index : Fin 16, channelCoefficient operator index • indexedChannel index = operator := by
  calc
    ∑ index : Fin 16, channelCoefficient operator index • indexedChannel index =
        ∑ index : Fin 16, (indexedChannelBasis.repr operator) index • indexedChannel index := by
          apply Finset.sum_congr rfl
          intro index _
          rw [channelCoefficient_eq_basis_repr]
    _ = operator := by
      simpa using Module.Basis.sum_repr indexedChannelBasis operator

theorem coefficients_injective : Function.Injective channelCoefficient := by
  intro first second equality
  calc
    first = ∑ index : Fin 16, channelCoefficient first index • indexedChannel index :=
      (channel_reconstruction first).symm
    _ = ∑ index : Fin 16, channelCoefficient second index • indexedChannel index := by
      rw [equality]
    _ = second := channel_reconstruction second

def diracDyad (left right : DiracSpinor) : DiracMatrix :=
  vecMulVec right (vecMul (star left) gamma0)

def bilinear (left : DiracSpinor) (insertion : DiracMatrix) (right : DiracSpinor) : ℂ :=
  dotProduct (star left) ((gamma0 * insertion).mulVec right)

theorem trace_dyad_eq_bilinear (left right : DiracSpinor) (insertion : DiracMatrix) :
    trace (insertion * diracDyad left right) = bilinear left insertion right := by
  simp [diracDyad, bilinear, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem fierz_dyad_reconstruction (left right : DiracSpinor) :
    diracDyad left right =
      ∑ index : Fin 16,
        (bilinear left (indexedChannel index).conjTranspose right / 4) •
          indexedChannel index := by
  rw [← channel_reconstruction (diracDyad left right)]
  apply Finset.sum_congr rfl
  intro index member
  rw [channelCoefficient, trace_dyad_eq_bilinear]

set_option maxHeartbeats 2000000 in
theorem channel_chirality (label : DiracBilinearLabel) :
    gamma5 * diracBilinearMatrix label =
      (-1 : ℂ) ^ cliffordDegree label • (diracBilinearMatrix label * gamma5) := by
  cases label with
  | scalar => simp [diracBilinearMatrix, cliffordDegree]
  | pseudoscalar => norm_num [diracBilinearMatrix, cliffordDegree]
  | vector coordinate =>
      fin_cases coordinate <;> ext row column <;>
        fin_cases row <;> fin_cases column <;>
        norm_num [diracBilinearMatrix, cliffordDegree, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
          Matrix.mul_apply, Fin.sum_univ_succ]
  | axial coordinate =>
      fin_cases coordinate <;> ext row column <;>
        fin_cases row <;> fin_cases column <;>
        norm_num [diracBilinearMatrix, cliffordDegree, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
          Matrix.mul_apply, Fin.sum_univ_succ]
  | bivector plane =>
      cases plane <;> ext row column <;>
        fin_cases row <;> fin_cases column <;>
        norm_num [diracBilinearMatrix, cliffordDegree, bivectorLeft, bivectorRight,
          gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
          Matrix.mul_apply, Fin.sum_univ_succ]

def weylChirality : InfoGeometry.OperatorAlgebra.ChiralInvolution DiracMatrix :=
  ⟨gamma5, gamma5_mul_self⟩

theorem gamma_odd (coordinate : Fin 4) :
    gamma coordinate * weylChirality.chi = -(weylChirality.chi * gamma coordinate) := by
  have anticommutes : gamma5 * gamma coordinate + gamma coordinate * gamma5 = 0 := by
    fin_cases coordinate
    · exact gamma5_gamma0_anticomm
    · exact gamma5_gamma1_anticomm
    · exact gamma5_gamma2_anticomm
    · exact gamma5_gamma3_anticomm
  rw [add_comm] at anticommutes
  exact add_eq_zero_iff_eq_neg.mp anticommutes

theorem vector_current_cross_corners_zero (coordinate : Fin 4) :
    weylChirality.Pleft * (gamma0 * gamma coordinate) * weylChirality.Pright = 0 ∧
      weylChirality.Pright * (gamma0 * gamma coordinate) * weylChirality.Pleft = 0 := by
  have selection := SpinorBilinearSelection.vector_selection weylChirality gamma0
    (gamma coordinate) (gamma_odd 0) (gamma_odd coordinate)
  exact ⟨selection.1, selection.2.1⟩

end InfoGeometry.CliffordWeyl.DiracBilinearChannels
