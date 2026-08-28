import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset Matrix

namespace KuboMoriBogoliubov

variable {n : ℕ}

/-- Faithful Quantum Density State ρ = diag(p₁, ..., pₙ) with strictly positive eigenvalues p_i > 0. -/
structure FaithfulDensityState (n : Type*) [Fintype n] [DecidableEq n] where
  eigenvalues : n → ℝ
  p_pos : ∀ i, 0 < eigenvalues i
  p_sum : ∑ i : n, eigenvalues i = 1

namespace FaithfulDensityState

variable {n : Type*} [Fintype n] [DecidableEq n] (rho : FaithfulDensityState n)

/-- Logarithmic Mean Weight c(p_i, p_j) for Kubo-Mori-Bogoliubov Metric.
    c(p_i, p_j) = (p_i - p_j) / (ln p_i - ln p_j) for p_i ≠ p_j, and p_i for p_i = p_j. -/
def bkmWeight (i j : n) : ℝ :=
  if rho.eigenvalues i = rho.eigenvalues j then
    rho.eigenvalues i
  else
    (rho.eigenvalues i - rho.eigenvalues j) / (Real.log (rho.eigenvalues i) - Real.log (rho.eigenvalues j))

/-- **Theorem**: BKM Weight Symmetry: c(p_i, p_j) = c(p_j, p_i). -/
theorem bkm_weight_symmetric (i j : n) :
    rho.bkmWeight i j = rho.bkmWeight j i := by
  dsimp [bkmWeight]
  by_cases h : rho.eigenvalues i = rho.eigenvalues j
  · have h_rev : rho.eigenvalues j = rho.eigenvalues i := h.symm
    rw [if_pos h, if_pos h_rev, h]
  · have h_rev : ¬(rho.eigenvalues j = rho.eigenvalues i) := fun h_eq => h h_eq.symm
    rw [if_neg h, if_neg h_rev]
    have h_num : rho.eigenvalues i - rho.eigenvalues j = - (rho.eigenvalues j - rho.eigenvalues i) := by ring
    have h_den : Real.log (rho.eigenvalues i) - Real.log (rho.eigenvalues j) = - (Real.log (rho.eigenvalues j) - Real.log (rho.eigenvalues i)) := by ring
    rw [h_num, h_den, neg_div_neg_eq]

/-- **Theorem**: BKM Weight Positivity for Equal Eigenvalues: c(p_i, p_i) > 0. -/
theorem bkm_weight_pos_diag (i : n) : 0 < rho.bkmWeight i i := by
  dsimp [bkmWeight]
  rw [if_pos rfl]
  exact rho.p_pos i

theorem bkm_weight_pos (i j : n) : 0 < rho.bkmWeight i j := by
  dsimp [bkmWeight]
  by_cases h_eq : rho.eigenvalues i = rho.eigenvalues j
  · rw [if_pos h_eq]
    exact rho.p_pos i
  · rw [if_neg h_eq]
    rcases lt_or_gt_of_ne h_eq with hlt | hgt
    · have hlog : Real.log (rho.eigenvalues i) <
          Real.log (rho.eigenvalues j) :=
        Real.strictMonoOn_log (rho.p_pos i) (rho.p_pos j) hlt
      exact div_pos_of_neg_of_neg (sub_neg.mpr hlt) (sub_neg.mpr hlog)
    · have hlog : Real.log (rho.eigenvalues j) <
          Real.log (rho.eigenvalues i) :=
        Real.strictMonoOn_log (rho.p_pos j) (rho.p_pos i) hgt
      exact div_pos (sub_pos.mpr hgt) (sub_pos.mpr hlog)

/-- Genuine Kubo-Mori-Bogoliubov (BKM) Inner Product on Matrix Operators:
    <A, B>_{BKM, ρ} = ∑_{i, j} A_ji * B_ji * c(p_i, p_j). -/
def bkmInnerProduct (A B : Matrix n n ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, A j i * B j i * rho.bkmWeight i j

/-- **Theorem**: Genuine BKM Metric Symmetry: <A, B>_{BKM, ρ} = <B, A>_{BKM, ρ}. -/
theorem bkm_metric_symmetry (A B : Matrix n n ℝ) :
    rho.bkmInnerProduct A B = rho.bkmInnerProduct B A := by
  dsimp [bkmInnerProduct]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [rho.bkm_weight_symmetric i j]
  ring

/-- **Theorem**: Genuine BKM Metric Non-Negativity for Diagonal Elements:
    <A, A>_{BKM, ρ} ≥ 0 for equal-eigenvalue density subspaces. -/
theorem bkm_metric_pos_semidef_diag (A : Matrix n n ℝ)
    (h_pos_weight : ∀ i j, 0 ≤ rho.bkmWeight i j) :
    0 ≤ rho.bkmInnerProduct A A := by
  dsimp [bkmInnerProduct]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have h_sq : 0 ≤ (A j i) ^ 2 := sq_nonneg (A j i)
  have h_prod : A j i * A j i * rho.bkmWeight i j = (A j i) ^ 2 * rho.bkmWeight i j := by ring
  rw [h_prod]
  exact mul_nonneg h_sq (h_pos_weight i j)

/-- Strict positivity of the diagonal spectral BKM form.  The hypothesis on
  every logarithmic-mean weight is explicit; this theorem does not promote
  the diagonal spectral model to the general noncommutative pairing. -/
theorem bkm_metric_pos_definite_diag (A : Matrix n n ℝ)
    (h_pos_weight : ∀ i j, 0 < rho.bkmWeight i j)
    (hA : A ≠ 0) :
    0 < rho.bkmInnerProduct A A := by
  have h_entry : ∃ i, ∃ j, A j i ≠ 0 := by
    by_contra h
    apply hA
    ext j i
    by_contra hij
    exact h ⟨i, ⟨j, hij⟩⟩
  obtain ⟨i₀, j₀, hA₀⟩ := h_entry
  dsimp [bkmInnerProduct]
  have h_inner :
      0 < ∑ j : n, A j i₀ * A j i₀ * rho.bkmWeight i₀ j := by
    refine Finset.sum_pos' ?_ ⟨j₀, Finset.mem_univ _, ?_⟩
    · intro j hj
      exact mul_nonneg (mul_self_nonneg (A j i₀))
        (le_of_lt (h_pos_weight i₀ j))
    · exact mul_pos (mul_self_pos.mpr hA₀) (h_pos_weight i₀ j₀)
  refine Finset.sum_pos' ?_ ⟨i₀, Finset.mem_univ _, h_inner⟩
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_self_nonneg (A j i))
    (le_of_lt (h_pos_weight i j))

theorem bkm_metric_pos_definite (A : Matrix n n ℝ) (hA : A ≠ 0) :
    0 < rho.bkmInnerProduct A A := by
  exact rho.bkm_metric_pos_definite_diag A
    (fun i j => rho.bkm_weight_pos i j) hA

def bkmLeftPairing (A : Matrix n n ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun := rho.bkmInnerProduct A
  map_add' B C := by
    simp [bkmInnerProduct, Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' r B := by
    simp [bkmInnerProduct, ← Finset.mul_sum, mul_assoc, mul_left_comm]

@[simp] theorem bkmLeftPairing_apply (A B : Matrix n n ℝ) :
    rho.bkmLeftPairing A B = rho.bkmInnerProduct A B :=
  rfl

def bkmPairingMap : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun := rho.bkmLeftPairing
  map_add' A B := by
    ext C
    change rho.bkmInnerProduct (A + B) C =
      rho.bkmInnerProduct A C + rho.bkmInnerProduct B C
    rw [rho.bkm_metric_symmetry A C, rho.bkm_metric_symmetry B C,
      rho.bkm_metric_symmetry (A + B) C]
    simp [bkmInnerProduct, Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' r A := by
    ext B
    change rho.bkmInnerProduct (r • A) B = r * rho.bkmInnerProduct A B
    rw [rho.bkm_metric_symmetry (r • A) B,
      rho.bkm_metric_symmetry A B]
    simp [bkmInnerProduct, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem bkmLeftPairing_injective :
    Function.Injective (rho.bkmLeftPairing) := by
  intro A B hAB
  by_contra hne
  let C : Matrix n n ℝ := A - B
  have hC : C ≠ 0 := by
    exact sub_ne_zero.mpr hne
  have hpos : 0 < rho.bkmInnerProduct C C :=
    rho.bkm_metric_pos_definite C hC
  have hzero : rho.bkmInnerProduct C C = 0 := by
    calc
      rho.bkmInnerProduct C C =
          rho.bkmInnerProduct C A - rho.bkmInnerProduct C B := by
        change rho.bkmLeftPairing C (A - B) = _
        rw [map_sub]
        simp only [bkmLeftPairing_apply]
      _ = rho.bkmInnerProduct A C - rho.bkmInnerProduct B C := by
        rw [rho.bkm_metric_symmetry C A, rho.bkm_metric_symmetry C B]
      _ = 0 := by
        have hA := congrArg (fun f : Matrix n n ℝ →ₗ[ℝ] ℝ => f C) hAB
        change rho.bkmInnerProduct A C - rho.bkmInnerProduct B C = 0
        have hA' : rho.bkmInnerProduct A C = rho.bkmInnerProduct B C := by
          simpa only [bkmLeftPairing_apply] using hA
        linarith
  linarith

theorem bkmLeftPairing_bijective :
    Function.Bijective (rho.bkmLeftPairing) := by
  have hdim :
      Module.finrank ℝ (Matrix n n ℝ) =
        Module.finrank ℝ (Matrix n n ℝ →ₗ[ℝ] ℝ) := by
    exact Subspace.dual_finrank_eq.symm
  refine ⟨rho.bkmLeftPairing_injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := rho.bkmPairingMap) hdim).mp
    (fun A B h => rho.bkmLeftPairing_injective (by simpa using h))

noncomputable def bkmPairingEquiv :
    Matrix n n ℝ ≃ₗ[ℝ] (Matrix n n ℝ →ₗ[ℝ] ℝ) :=
  LinearEquiv.ofBijective rho.bkmPairingMap rho.bkmLeftPairing_bijective

@[simp] theorem bkmPairingEquiv_apply (A : Matrix n n ℝ) :
    rho.bkmPairingEquiv A = rho.bkmPairingMap A :=
  rfl

theorem bkmPairingEquiv_inverse_left (A : Matrix n n ℝ) :
    rho.bkmPairingEquiv.symm (rho.bkmPairingEquiv A) = A := by
  exact rho.bkmPairingEquiv.left_inv A

theorem bkmPairingEquiv_inverse_right
    (F : Matrix n n ℝ →ₗ[ℝ] ℝ) :
    rho.bkmPairingEquiv (rho.bkmPairingEquiv.symm F) = F := by
  exact rho.bkmPairingEquiv.right_inv F

end FaithfulDensityState

end KuboMoriBogoliubov
