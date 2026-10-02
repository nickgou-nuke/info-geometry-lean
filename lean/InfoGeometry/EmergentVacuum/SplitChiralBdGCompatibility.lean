import InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
import InfoGeometry.Canonical.ZornBdGHamiltonianChiralBridge
import InfoGeometry.CliffordWeyl.ChiralIdeals
import InfoGeometry.SuperMetriplectic.Flow

noncomputable section

namespace InfoGeometry.EmergentVacuum.SplitChiralBdGCompatibility

open InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
open InfoGeometry.Canonical.KreinDoubledCartanPeirce
open InfoGeometry.Canonical.ZornBdGHamiltonianChiral
open InfoGeometry.OperatorAlgebra

def splitChirality : ChiralInvolution Mat2 := ⟨K_mat, K_sq⟩

theorem grading_eq_krein_symmetry : splitChirality.chi = eta (R := ℝ) := rfl

theorem left_projector_eq_peirce : splitChirality.Pleft = P_plus (R := ℝ) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [splitChirality, ChiralInvolution.Pleft, K_mat, P_plus]

theorem right_projector_eq_peirce : splitChirality.Pright = P_minus (R := ℝ) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [splitChirality, ChiralInvolution.Pright, K_mat, P_minus]

theorem kinetic_eq_split_axis (momentum : ℝ) :
    zornChiralDirac momentum = momentum • K_mat := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [zornChiralDirac, K_mat]

theorem pairing_eq_split_axis (pairing : ℝ) :
    zornPairing pairing pairing = pairing • J_mat := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [zornPairing, J_mat]

theorem bdg_eq_split_axes (momentum pairing : ℝ) :
    zornBdG momentum pairing pairing = momentum • K_mat + pairing • J_mat := by
  rw [zornBdG_decomp, kinetic_eq_split_axis, pairing_eq_split_axis]

theorem pairing_swaps_projectors (upper lower : ℝ) :
    splitChirality.Pleft * zornPairing upper lower =
      zornPairing upper lower * splitChirality.Pright := by
  apply InfoGeometry.CliffordWeyl.Pleft_mul_swap
  have anticommutes := eta_pairing_anticomm upper lower
  rw [add_comm] at anticommutes
  exact add_eq_zero_iff_eq_neg.mp anticommutes

theorem pairing_diagonal_corners_zero (upper lower : ℝ) :
    splitChirality.Pleft * zornPairing upper lower * splitChirality.Pleft = 0 ∧
      splitChirality.Pright * zornPairing upper lower * splitChirality.Pright = 0 := by
  apply InfoGeometry.CliffordWeyl.diagonal_corners_zero
  have anticommutes := eta_pairing_anticomm upper lower
  rw [add_comm] at anticommutes
  exact add_eq_zero_iff_eq_neg.mp anticommutes

theorem bdg_square (momentum pairing : ℝ) :
    zornBdG momentum pairing pairing * zornBdG momentum pairing pairing =
      (momentum ^ 2 + pairing ^ 2) • (1 : Mat2) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [zornBdG, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem equilibrium_bdg_square
    (flow : InfoGeometry.SuperMetriplectic.MetriplecticFlow Mat2)
    (momentum pairing : ℝ)
    (equilibrium : flow.IsDissipativeEquilibrium)
    (reversible : flow.reversibleFlow = zornBdG momentum pairing pairing) :
    flow.totalFlow * flow.totalFlow =
      (momentum ^ 2 + pairing ^ 2) • (1 : Mat2) := by
  rw [flow.totalFlow_eq_reversible_add_dissipative,
    flow.dissipativeFlow_eq_zero_of_equilibrium equilibrium, add_zero, reversible]
  exact bdg_square momentum pairing

theorem secular_pairing_lower_bound (momentum pairing energy : ℝ)
    (secular : Matrix.det (zornBdG momentum pairing pairing - energy • 1) = 0) :
    pairing ^ 2 ≤ energy ^ 2 := by
  rw [(zornBdG_symmetric_secular momentum pairing energy).mp secular]
  exact le_add_of_nonneg_left (sq_nonneg momentum)

end InfoGeometry.EmergentVacuum.SplitChiralBdGCompatibility
