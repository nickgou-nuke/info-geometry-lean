import InfoGeometry.Lie.CanonicalZornG2CartanMassieuStable
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2MassieuConvexity
import InfoGeometry.Analytic.LogSumExpVariancePositivity

noncomputable section

open scoped BigOperators
open InfoGeometry.Analytic
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornG2CartanMassieuStable
open InfoGeometry.Lie.CanonicalZornG2MassieuConvexity

namespace InfoGeometry.Lie.CanonicalZornG2CartanFisherStable

variable {State : Type*} [Fintype State] [Nonempty State]
  (D : CartanSouriauDatum State)

/-- The diagonal Fisher--Souriau covariance of one Cartan charge. -/
def diagonalCovariance (beta : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x *
    (D.momentMap x i - meanCharge D beta i) ^ (2 : ℕ)

/-- The full finite Fisher--Souriau covariance matrix. -/
def covariance (beta : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x *
    (D.momentMap x i - meanCharge D beta i) *
    (D.momentMap x j - meanCharge D beta j)

def directionalVariance (beta v : Fin 2 → ℝ) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x *
    (∑ i : Fin 2, v i * (D.momentMap x i - meanCharge D beta i)) ^
      (2 : ℕ)

theorem directionalVariance_nonneg (beta v : Fin 2 → ℝ) :
    0 ≤ directionalVariance D beta v := by
  unfold directionalVariance
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg
    (le_of_lt (div_pos (Real.exp_pos _) (realGibbsPartition_pos D beta)))
    (sq_nonneg _)

theorem directionalVariance_eq_covarianceQuadratic
    (beta v : Fin 2 → ℝ) :
    directionalVariance D beta v =
      ∑ i : Fin 2, ∑ j : Fin 2,
        v i * covariance D beta i j * v j := by
  unfold directionalVariance covariance
  simp_rw [pow_two]
  rw [show (∑ x : State, realGibbsWeight D beta x *
      ((∑ i : Fin 2, v i *
        (D.momentMap x i - meanCharge D beta i)) *
       (∑ j : Fin 2, v j *
        (D.momentMap x j - meanCharge D beta j)))) =
      ∑ x : State, ∑ i : Fin 2, ∑ j : Fin 2,
        realGibbsWeight D beta x *
          (v i * (D.momentMap x i - meanCharge D beta i)) *
          (v j * (D.momentMap x j - meanCharge D beta j)) by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ x, realGibbsWeight D beta x *
        (v i * (D.momentMap x i - meanCharge D beta i)) *
        (v j * (D.momentMap x j - meanCharge D beta j))) =
        ∑ x, v i * (realGibbsWeight D beta x *
          (D.momentMap x i - meanCharge D beta i) *
          (D.momentMap x j - meanCharge D beta j)) * v j := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (v i * ∑ x, realGibbsWeight D beta x *
          (D.momentMap x i - meanCharge D beta i) *
          (D.momentMap x j - meanCharge D beta j)) * v j := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem covariance_comm (beta : Fin 2 → ℝ) (i j : Fin 2) :
    covariance D beta i j = covariance D beta j i := by
  unfold covariance
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem covariance_diag (beta : Fin 2 → ℝ) (i : Fin 2) :
    covariance D beta i i = diagonalCovariance D beta i := by
  unfold covariance diagonalCovariance
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem second_partial_eq_diagonalCovariance
    (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => potential D (slice beta i t')) t) (beta i) =
      diagonalCovariance D beta i := by
  rw [second_partial_eq_variance D beta i]
  let w : State → ℝ := fun x => Real.exp
    (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))
  let a : State → ℝ := fun x => -D.momentMap x i
  change logSumExpVariance w a (beta i) = diagonalCovariance D beta i
  have hw : ∀ x, 0 < w x := by
    intro x
    exact Real.exp_pos _
  have hpart : logSumExpPartition w a (beta i) = realGibbsPartition D beta := by
    unfold logSumExpPartition realGibbsPartition w a realGibbsKernel
      realPairingEnergy
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    simp only [realPairingEnergy, Fin.sum_univ_two]
    fin_cases i <;> simp <;> ring
  have hweight : ∀ x, logSumExpWeight w a (beta i) x =
      realGibbsWeight D beta x := by
    intro x
    unfold logSumExpWeight realGibbsWeight realGibbsKernel
    rw [hpart]
    rw [← Real.exp_add]
    congr 1
    simp only [realPairingEnergy, Fin.sum_univ_two]
    dsimp [a]
    fin_cases i <;> simp <;> ring
  rw [logSumExpVariance_eq_centered w a hw (beta i)]
  have hmean :
      (∑ x : State, logSumExpWeight w a (beta i) x * a x) =
        -meanCharge D beta i := by
    simp_rw [hweight]
    unfold a meanCharge
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  rw [hmean]
  simp_rw [hweight]
  unfold diagonalCovariance
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  dsimp [a]
  ring

theorem diagonalCovariance_nonneg (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ diagonalCovariance D beta i := by
  rw [← second_partial_eq_diagonalCovariance D beta i]
  exact second_partial_nonneg D beta i

theorem covariance_diag_nonneg (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ covariance D beta i i := by
  rw [covariance_diag D beta i]
  exact diagonalCovariance_nonneg D beta i

theorem diagonalCovariance_pos_of_charge_ne
    (beta : Fin 2 → ℝ) (i : Fin 2)
    (hne : ∃ x y : State, D.momentMap x i ≠ D.momentMap y i) :
    0 < diagonalCovariance D beta i := by
  rw [← second_partial_eq_diagonalCovariance D beta i]
  exact second_partial_pos_of_charge_ne D beta i hne

end InfoGeometry.Lie.CanonicalZornG2CartanFisherStable
