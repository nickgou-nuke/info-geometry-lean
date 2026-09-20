import InfoGeometry.Clifford.CrawfordDiracBispinorDensities
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.CliffordWeyl.SpinorBilinearSelection

noncomputable section

namespace InfoGeometry.CliffordWeyl.DiracBilinearChannels

open InfoGeometry.Clifford.CrawfordDiracBispinorDensities
open Matrix

def channel : DiracBilinearLabel → DiracMatrix
  | .scalar => 1
  | .pseudoscalar => gamma5
  | .vector coordinate => gamma coordinate
  | .axial coordinate => gamma coordinate * gamma5
  | .bivector plane => gamma (bivectorLeft plane) * gamma (bivectorRight plane)

def cliffordDegree : DiracBilinearLabel → ℕ
  | .scalar => 0
  | .vector _ => 1
  | .bivector _ => 2
  | .axial _ => 3
  | .pseudoscalar => 4

def indexedChannel (index : Fin 16) : DiracMatrix :=
  channel (finToDiracBilinearLabel index)

def channelCoefficient (operator : DiracMatrix) (index : Fin 16) : ℂ :=
  trace ((indexedChannel index).conjTranspose * operator) / 4

set_option maxHeartbeats 2000000 in
theorem channel_reconstruction (operator : DiracMatrix) :
    ∑ index : Fin 16, channelCoefficient operator index • indexedChannel index = operator := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [channelCoefficient, indexedChannel, channel, finToDiracBilinearLabel,
      bivectorLeft, bivectorRight, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

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

theorem channel_chirality (label : DiracBilinearLabel) :
    gamma5 * channel label =
      (-1 : ℂ) ^ cliffordDegree label • (channel label * gamma5) := by
  cases label with
  | scalar => simp [channel, cliffordDegree]
  | pseudoscalar => norm_num [channel, cliffordDegree]
  | vector coordinate =>
      fin_cases coordinate <;> ext row column <;>
        fin_cases row <;> fin_cases column <;>
        norm_num [channel, cliffordDegree, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
          Matrix.mul_apply, Fin.sum_univ_succ]
  | axial coordinate =>
      fin_cases coordinate <;> ext row column <;>
        fin_cases row <;> fin_cases column <;>
        norm_num [channel, cliffordDegree, gamma, gamma0, gamma1, gamma2, gamma3, gamma5,
          Matrix.mul_apply, Fin.sum_univ_succ]
  | bivector plane =>
      cases plane <;> ext row column <;>
        fin_cases row <;> fin_cases column <;>
        norm_num [channel, cliffordDegree, bivectorLeft, bivectorRight,
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
