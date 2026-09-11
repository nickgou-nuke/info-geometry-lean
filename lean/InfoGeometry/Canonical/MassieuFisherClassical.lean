import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Analytic.LogSumExpVariancePositivity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie
open InfoGeometry.Analytic
open scoped BigOperators

namespace InfoGeometry.Canonical.MassieuFisherClassical

variable {State : Type*} [Fintype State] [Nonempty State]

def βSlice (beta : Fin 2 → ℝ) (i : Fin 2) (t : ℝ) : Fin 2 → ℝ :=
  fun j => if j = i then t else beta j

noncomputable def chargeCovariance
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x * 
    (D.momentMap x i - souriauChargeMean D beta i) * (D.momentMap x j - souriauChargeMean D beta j)

def FisherMatrix
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => chargeCovariance D beta i j

/-- Lemma connecting diagonal chargeCovariance to souriauChargeVariance -/
lemma chargeCovariance_diag_eq_chargeVariance
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    chargeCovariance D beta i i = souriauChargeVariance D beta i := by
  dsimp [chargeCovariance, souriauChargeVariance]
  congr 1
  ext x
  ring

theorem fisherMatrix_diag_eq_chargeVariance
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    FisherMatrix D beta i i = souriauChargeVariance D beta i := by
  exact chargeCovariance_diag_eq_chargeVariance D beta i

/-- THEOREM 1: Massieu Hessian = Charge Covariance (diagonal case) -/
theorem hessian_diag_eq_cov
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv (fun t' => souriauMassieu D (βSlice beta i t')) t) (beta i) =
      chargeCovariance D beta i i := by
  have h := souriauMassieu_secondDeriv_eq_chargeVariance D beta i
  rw [chargeCovariance_diag_eq_chargeVariance]
  simpa [βSlice] using h

/-- THEOREM 2: Massieu Hessian (diagonal) is Positive Semidefinite -/
theorem hessian_diag_pos_semidef
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ deriv (fun t => deriv (fun t' => souriauMassieu D (βSlice beta i t')) t) (beta i) := by
  have h := souriauMassieu_secondDeriv_nonneg D beta i
  simpa [βSlice] using h

/-- THEOREM 3: Full Fisher Matrix is Positive Semidefinite (PSD).
    Every quadratic form vᵀ F v = ∑_x w_x (∑_i v_i (μ_x(i) - μ̄(i)))² ≥ 0. -/
theorem fisher_pos_semidef
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (v : Fin 2 → ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, v i * chargeCovariance D beta i j * v j := by
  have h_identity : (∑ i : Fin 2, ∑ j : Fin 2, v i * chargeCovariance D beta i j * v j) =
      ∑ x : State, realGibbsWeight D beta x *
        (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := by
    dsimp [chargeCovariance]
    calc
      ∑ i : Fin 2, ∑ j : Fin 2, v i * (∑ x : State, realGibbsWeight D beta x *
          (D.momentMap x i - souriauChargeMean D beta i) *
          (D.momentMap x j - souriauChargeMean D beta j)) * v j
        = ∑ i : Fin 2, ∑ j : Fin 2, ∑ x : State,
            realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = ∑ i : Fin 2, ∑ x : State, ∑ j : Fin 2,
            realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
      _ = ∑ x : State, ∑ i : Fin 2, ∑ j : Fin 2,
            realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          rw [Finset.sum_comm]
      _ = ∑ x : State, realGibbsWeight D beta x *
            (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (∑ j : Fin 2, v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            ∑ i : Fin 2, ∑ j : Fin 2,
                realGibbsWeight D beta x *
                (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
                (v j * (D.momentMap x j - souriauChargeMean D beta j))
              = ∑ i : Fin 2, (realGibbsWeight D beta x * (v i * (D.momentMap x i - souriauChargeMean D beta i))) *
                  ∑ j : Fin 2, (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [← Finset.mul_sum]
            _ = (∑ i : Fin 2, (realGibbsWeight D beta x * (v i * (D.momentMap x i - souriauChargeMean D beta i)))) *
                  ∑ j : Fin 2, (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
                rw [← Finset.sum_mul]
            _ = realGibbsWeight D beta x *
                  (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) *
                  (∑ j : Fin 2, v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
                rw [← Finset.mul_sum]
      _ = ∑ x : State, realGibbsWeight D beta x *
            (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          ring
  rw [h_identity]
  apply Finset.sum_nonneg
  intro x _
  have hw : 0 ≤ realGibbsWeight D beta x := by
    unfold realGibbsWeight
    exact div_nonneg (Real.exp_pos _).le (realGibbsPartition_pos D beta).le
  have hsq : 0 ≤ (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := sq_nonneg _
  exact mul_nonneg hw hsq

/-- THEOREM 4: Full Fisher Matrix is Strictly Positive Definite (PD) under Separating Charges.
    If charges separate microstates, then for all v ≠ 0, vᵀ F v > 0. -/
theorem fisher_pos_def_of_separating
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (hseparates : ∀ w : Fin 2 → ℝ, w ≠ 0 →
      ∃ x y : State, (∑ i : Fin 2, w i * (D.momentMap x i - D.momentMap y i)) ≠ 0) :
    0 < ∑ i : Fin 2, ∑ j : Fin 2, v i * chargeCovariance D beta i j * v j := by
  have h_identity : (∑ i : Fin 2, ∑ j : Fin 2, v i * chargeCovariance D beta i j * v j) =
      ∑ x : State, realGibbsWeight D beta x *
        (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := by
    dsimp [chargeCovariance]
    calc
      ∑ i : Fin 2, ∑ j : Fin 2, v i * (∑ x : State, realGibbsWeight D beta x *
          (D.momentMap x i - souriauChargeMean D beta i) *
          (D.momentMap x j - souriauChargeMean D beta j)) * v j
        = ∑ i : Fin 2, ∑ j : Fin 2, ∑ x : State,
            realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = ∑ i : Fin 2, ∑ x : State, ∑ j : Fin 2,
            realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
      _ = ∑ x : State, ∑ i : Fin 2, ∑ j : Fin 2,
            realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          rw [Finset.sum_comm]
      _ = ∑ x : State, realGibbsWeight D beta x *
            (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) *
            (∑ j : Fin 2, v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            ∑ i : Fin 2, ∑ j : Fin 2,
                realGibbsWeight D beta x *
                (v i * (D.momentMap x i - souriauChargeMean D beta i)) *
                (v j * (D.momentMap x j - souriauChargeMean D beta j))
              = ∑ i : Fin 2, (realGibbsWeight D beta x * (v i * (D.momentMap x i - souriauChargeMean D beta i))) *
                  ∑ j : Fin 2, (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [← Finset.mul_sum]
            _ = (∑ i : Fin 2, (realGibbsWeight D beta x * (v i * (D.momentMap x i - souriauChargeMean D beta i)))) *
                  ∑ j : Fin 2, (v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
                rw [← Finset.sum_mul]
            _ = realGibbsWeight D beta x *
                  (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) *
                  (∑ j : Fin 2, v j * (D.momentMap x j - souriauChargeMean D beta j)) := by
                rw [← Finset.mul_sum]
      _ = ∑ x : State, realGibbsWeight D beta x *
            (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          ring
  rw [h_identity]
  have h_nonneg : ∀ x ∈ (Finset.univ : Finset State),
      0 ≤ realGibbsWeight D beta x *
        (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := by
    intro x _
    have hw : 0 ≤ realGibbsWeight D beta x := by
      unfold realGibbsWeight
      exact div_nonneg (Real.exp_pos _).le (realGibbsPartition_pos D beta).le
    have hsq : 0 ≤ (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 := sq_nonneg _
    exact mul_nonneg hw hsq
  rcases hseparates v hv with ⟨x, y, hdiff⟩
  have h_not_both_zero :
      (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ≠ 0 ∨
      (∑ i : Fin 2, v i * (D.momentMap y i - souriauChargeMean D beta i)) ≠ 0 := by
    by_contra h_both_zero
    push_neg at h_both_zero
    rcases h_both_zero with ⟨hx, hy⟩
    have h_sub : (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) -
                 (∑ i : Fin 2, v i * (D.momentMap y i - souriauChargeMean D beta i)) = 0 := by
      rw [hx, hy, sub_self]
    have h_sub_eq : (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) -
                    (∑ i : Fin 2, v i * (D.momentMap y i - souriauChargeMean D beta i)) =
                    ∑ i : Fin 2, v i * (D.momentMap x i - D.momentMap y i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_sub_eq] at h_sub
    exact hdiff h_sub
  have h_exists_pos : ∃ x0 ∈ (Finset.univ : Finset State),
      0 < realGibbsWeight D beta x0 *
        (∑ i : Fin 2, v i * (D.momentMap x0 i - souriauChargeMean D beta i)) ^ 2 := by
    cases h_not_both_zero with
    | inl hx =>
      refine ⟨x, Finset.mem_univ x, ?_⟩
      have hw_pos : 0 < realGibbsWeight D beta x := by
        unfold realGibbsWeight
        exact div_pos (Real.exp_pos _) (realGibbsPartition_pos D beta)
      have hsq_pos : 0 < (∑ i : Fin 2, v i * (D.momentMap x i - souriauChargeMean D beta i)) ^ 2 :=
        sq_pos_of_ne_zero hx
      exact mul_pos hw_pos hsq_pos
    | inr hy =>
      refine ⟨y, Finset.mem_univ y, ?_⟩
      have hw_pos : 0 < realGibbsWeight D beta y := by
        unfold realGibbsWeight
        exact div_pos (Real.exp_pos _) (realGibbsPartition_pos D beta)
      have hsq_pos : 0 < (∑ i : Fin 2, v i * (D.momentMap y i - souriauChargeMean D beta i)) ^ 2 :=
        sq_pos_of_ne_zero hy
      exact mul_pos hw_pos hsq_pos
  exact Finset.sum_pos' h_nonneg h_exists_pos

theorem fisherMatrix_symmetric
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    Matrix.transpose (FisherMatrix D beta) = FisherMatrix D beta := by
  ext i j
  dsimp [FisherMatrix, chargeCovariance, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem massieu_fisher_classical_master
    (D : CartanSouriauDatum State) (beta v : Fin 2 → ℝ) (i : Fin 2)
    (hv : v ≠ 0)
    (hseparates : ∀ w : Fin 2 → ℝ, w ≠ 0 →
      ∃ x y : State, (∑ j : Fin 2, w j * (D.momentMap x j - D.momentMap y j)) ≠ 0) :
    (deriv (fun t => deriv (fun t' => souriauMassieu D (βSlice beta i t')) t) (beta i) =
      chargeCovariance D beta i i) ∧
    (0 ≤ deriv (fun t => deriv (fun t' => souriauMassieu D (βSlice beta i t')) t) (beta i)) ∧
    (0 ≤ ∑ j : Fin 2, ∑ k : Fin 2, v j * chargeCovariance D beta j k * v k) ∧
    (0 < ∑ j : Fin 2, ∑ k : Fin 2, v j * chargeCovariance D beta j k * v k) := by
  exact ⟨hessian_diag_eq_cov D beta i,
    hessian_diag_pos_semidef D beta i,
    fisher_pos_semidef D beta v,
    fisher_pos_def_of_separating D beta v hv hseparates⟩

end InfoGeometry.Canonical.MassieuFisherClassical

end noncomputable section
