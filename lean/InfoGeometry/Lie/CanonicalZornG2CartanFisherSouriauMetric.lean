import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Analytic
open scoped BigOperators

namespace InfoGeometry.Lie

variable {State : Type*} [Fintype State] [Nonempty State] (D : CartanSouriauDatum State)

/-- Fisher-Souriau metric (covariance) under the finite Gibbs state. -/
def fisherSouriauMatrix (beta : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x *
    (D.momentMap x i - souriauChargeMean D beta i) *
    (D.momentMap x j - souriauChargeMean D beta j)

theorem fisherSouriauMatrix_symmetric
    (beta : Fin 2 → ℝ) (i j : Fin 2) :
    fisherSouriauMatrix D beta i j = fisherSouriauMatrix D beta j i := by
  unfold fisherSouriauMatrix
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma variance_algebra (E J : State → ℝ) (Z : ℝ) (hZ : Z = ∑ x, E x) (hZ0 : Z ≠ 0) :
    (∑ x, (E x / Z) * (J x - (∑ y, (E y / Z) * J y)) ^ 2) =
      (∑ x, E x * J x ^ 2) / Z - ((∑ y, E y * J y) / Z) ^ 2 := by
  set μ := (∑ y, E y * J y) / Z
  have h_mu : (∑ y, (E y / Z) * J y) = μ := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  rw [h_mu]
  have h1 : ∀ x, (E x / Z) * (J x - μ) ^ 2 = (E x / Z) * J x ^ 2 - 2 * μ * ((E x / Z) * J x) + μ ^ 2 * (E x / Z) := by
    intro x
    ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hZ_sum : (∑ x, E x / Z) = 1 := by
    rw [← Finset.sum_div, ← hZ, div_self hZ0]
  have hJ_sum : (∑ x, (E x / Z) * J x) = μ := by
    exact h_mu
  rw [hZ_sum, hJ_sum]
  have h_left : (∑ x, (E x / Z) * J x ^ 2) = (∑ x, E x * J x ^ 2) / Z := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  rw [h_left]
  ring

lemma fisherSouriauMatrix_diag_eq_logSumExpVariance (beta : Fin 2 → ℝ) (i : Fin 2) :
    fisherSouriauMatrix D beta i i =
      logSumExpVariance (fun x => Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
                        (fun x => -D.momentMap x i) (beta i) := by
  have h1 : fisherSouriauMatrix D beta i i = souriauChargeVariance D beta i := by
    unfold fisherSouriauMatrix souriauChargeVariance
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h1]
  have h2 : logSumExpVariance (fun x => Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))) (fun x => -D.momentMap x i) (beta i) = deriv (fun t => deriv (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) := (souriauMassieu_secondDeriv_eq_logSumExpVariance D beta i).symm
  have h3 : deriv (fun t => deriv (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) = souriauChargeVariance D beta i := souriauMassieu_secondDeriv_eq_chargeVariance D beta i
  exact (Eq.trans h2 h3).symm

/-- Second derivative equals charge variance (Hessian = Covariance matrix diagonal). -/
theorem fisherSouriauMatrix_eq_massieuHessian (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) =
      fisherSouriauMatrix D beta i i := by
  have hw : ∀ x, 0 < Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)) :=
    fun x => Real.exp_pos _
  have hd_eq : (fun t' => souriauMassieu D (betaSlice beta i t')) = 
               (fun t' => logSumExp (fun x => Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))) (fun x => -D.momentMap x i) t') := by
    ext t'
    exact souriauMassieu_slice_eq_logSumExp D beta i t'
  rw [hd_eq]
  rw [fisherSouriauMatrix_diag_eq_logSumExpVariance D beta i]
  exact logSumExp_secondDeriv_eq_variance (fun x => Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))) (fun x => -D.momentMap x i) hw (beta i)


/-- The Fisher-Souriau matrix is positive semi-definite on the diagonal. 
(Convexity in coordinate directions) -/
theorem fisherSouriauMatrix_posSemidefinite (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ fisherSouriauMatrix D beta i i := by
  rw [fisherSouriauMatrix_diag_eq_logSumExpVariance D beta i]
  have hw : ∀ x, 0 < Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)) :=
    fun x => Real.exp_pos _
  exact InfoGeometry.Analytic.logSumExpVariance_nonneg 
    (fun x => Real.exp (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
    (fun x => -D.momentMap x i) hw (beta i)

/-- Directional covariance quadratic form. -/
def fisherSouriauQuadratic (beta v : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    v i * fisherSouriauMatrix D beta i j * v j

def betaLine (beta v : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun j => beta j + t * v j

/-- The directional Fisher form is the Gibbs expectation of a square. -/
theorem fisherSouriauQuadratic_eq_directionalVariance
    (beta v : Fin 2 → ℝ) :
    fisherSouriauQuadratic D beta v =
      ∑ x : State, realGibbsWeight D beta x *
        (∑ i : Fin 2, v i *
          (D.momentMap x i - souriauChargeMean D beta i)) ^ (2 : ℕ) := by
  unfold fisherSouriauQuadratic fisherSouriauMatrix
  calc
    ∑ i : Fin 2, ∑ j : Fin 2,
        v i * (∑ x : State,
          realGibbsWeight D beta x *
            (D.momentMap x i - souriauChargeMean D beta i) *
            (D.momentMap x j - souriauChargeMean D beta j)) * v j
        = ∑ i : Fin 2, ∑ j : Fin 2, ∑ x : State,
          realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i) *
              (v j * (D.momentMap x j - souriauChargeMean D beta j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        v i * (∑ x : State,
            realGibbsWeight D beta x *
              (D.momentMap x i - souriauChargeMean D beta i) *
              (D.momentMap x j - souriauChargeMean D beta j)) * v j
            = (v i * v j) * ∑ x : State,
                realGibbsWeight D beta x *
                  (D.momentMap x i - souriauChargeMean D beta i) *
                  (D.momentMap x j - souriauChargeMean D beta j) := by ring
        _ = ∑ x : State, (v i * v j) *
                (realGibbsWeight D beta x *
                  (D.momentMap x i - souriauChargeMean D beta i) *
                  (D.momentMap x j - souriauChargeMean D beta j)) := by
              rw [Finset.mul_sum]
        _ = ∑ x : State, realGibbsWeight D beta x *
              (v i * (D.momentMap x i - souriauChargeMean D beta i) *
                (v j * (D.momentMap x j - souriauChargeMean D beta j))) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
    _ = ∑ i : Fin 2, ∑ x : State, ∑ j : Fin 2,
          realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i) *
              (v j * (D.momentMap x j - souriauChargeMean D beta j))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ x : State, ∑ i : Fin 2, ∑ j : Fin 2,
          realGibbsWeight D beta x *
            (v i * (D.momentMap x i - souriauChargeMean D beta i) *
              (v j * (D.momentMap x j - souriauChargeMean D beta j))) := by
      rw [Finset.sum_comm]
    _ = ∑ x : State, realGibbsWeight D beta x *
          (∑ i : Fin 2, v i *
            (D.momentMap x i - souriauChargeMean D beta i)) *
          (∑ j : Fin 2, v j *
            (D.momentMap x j - souriauChargeMean D beta j)) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ x : State, realGibbsWeight D beta x *
          (∑ i : Fin 2, v i *
            (D.momentMap x i - souriauChargeMean D beta i)) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- The full finite Fisher--Souriau covariance form is positive semidefinite. -/
theorem fisherSouriauQuadratic_nonneg (beta v : Fin 2 → ℝ) :
    0 ≤ fisherSouriauQuadratic D beta v := by
  rw [fisherSouriauQuadratic_eq_directionalVariance D beta v]
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg
    (le_of_lt (div_pos (Real.exp_pos _)
      (realGibbsPartition_pos D beta)))
      (sq_nonneg _)

/-
The finite Gibbs weights are strictly positive.  Consequently the only way
the directional covariance can vanish is that the centered directional charge
vanishes at every state.  This is the kernel statement underlying the later
non-degeneracy/strict-convexity criterion.
-/
theorem fisherSouriauQuadratic_eq_zero_iff
    (beta v : Fin 2 → ℝ) :
    fisherSouriauQuadratic D beta v = 0 ↔
      ∀ x : State,
        (∑ i : Fin 2, v i *
          (D.momentMap x i - souriauChargeMean D beta i)) = 0 := by
  rw [fisherSouriauQuadratic_eq_directionalVariance D beta v]
  constructor
  · intro hzero x
    by_contra hne
    have hpos : 0 < fisherSouriauQuadratic D beta v := by
      rw [fisherSouriauQuadratic_eq_directionalVariance D beta v]
      apply Finset.sum_pos' 
        (fun y _ => mul_nonneg
          (le_of_lt (div_pos (Real.exp_pos _)
            (realGibbsPartition_pos D beta)))
          (sq_nonneg _))
      exact ⟨x, Finset.mem_univ x,
        mul_pos
          (div_pos (Real.exp_pos _)
            (realGibbsPartition_pos D beta))
          (sq_pos_of_ne_zero hne)⟩
    rw [fisherSouriauQuadratic_eq_directionalVariance D beta v] at hpos
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  · intro hzero
    apply Finset.sum_eq_zero
    intro x hx
    simp [hzero x]

/-- Strict positivity in a direction whose centered charge is nonzero on some state. -/
theorem fisherSouriauQuadratic_pos_of_nonzero_direction
    (beta v : Fin 2 → ℝ)
    (h : ∃ x : State,
      (∑ i : Fin 2, v i *
        (D.momentMap x i - souriauChargeMean D beta i)) ≠ 0) :
    0 < fisherSouriauQuadratic D beta v := by
  rw [fisherSouriauQuadratic_eq_directionalVariance D beta v]
  have h_nonneg :
      ∀ x ∈ (Finset.univ : Finset State),
        0 ≤ realGibbsWeight D beta x *
          (∑ i : Fin 2, v i *
            (D.momentMap x i - souriauChargeMean D beta i)) ^ (2 : ℕ) := by
    intro x hx
    exact mul_nonneg
      (le_of_lt (div_pos (Real.exp_pos _)
        (realGibbsPartition_pos D beta)))
      (sq_nonneg _)
  rcases h with ⟨x0, hx0⟩
  have h_pos :
      ∃ x ∈ (Finset.univ : Finset State),
        0 < realGibbsWeight D beta x *
          (∑ i : Fin 2, v i *
            (D.momentMap x i - souriauChargeMean D beta i)) ^ (2 : ℕ) := by
    refine ⟨x0, Finset.mem_univ x0, ?_⟩
    exact mul_pos
      (div_pos (Real.exp_pos _) (realGibbsPartition_pos D beta))
      (sq_pos_of_ne_zero hx0)
  exact Finset.sum_pos' h_nonneg h_pos

/-
Affine nondegeneracy of the finite charge family implies strict positivity of
the Fisher--Souriau quadratic form in every nonzero direction.  The hypothesis
is stated directly as separation of charge vectors, so no unproved
identification with an affine-span API is required here.
-/
theorem fisherSouriauQuadratic_pos_of_charge_separates
    (beta v : Fin 2 → ℝ) (hv : v ≠ 0)
    (hseparates : ∀ w : Fin 2 → ℝ, w ≠ 0 →
      ∃ x y : State,
        (∑ i : Fin 2, w i *
          (D.momentMap x i - D.momentMap y i)) ≠ 0) :
    0 < fisherSouriauQuadratic D beta v := by
  apply fisherSouriauQuadratic_pos_of_nonzero_direction D beta v
  obtain ⟨x, y, hxy⟩ := hseparates v hv
  by_contra hzero
  push_neg at hzero
  apply hxy
  have hx := hzero x
  have hy := hzero y
  have hdiff :
      (∑ i : Fin 2, v i *
          (D.momentMap x i - D.momentMap y i)) =
        (∑ i : Fin 2, v i *
          (D.momentMap x i - souriauChargeMean D beta i)) -
        (∑ i : Fin 2, v i *
          (D.momentMap y i - souriauChargeMean D beta i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdiff, hx, hy]
  ring

/-- The second derivative of the Massieu potential along any Cartan direction
is the corresponding Fisher--Souriau quadratic form. -/
theorem souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic
    (beta v : Fin 2 → ℝ) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaLine beta v t')) t) 0 =
      fisherSouriauQuadratic D beta v := by
  let w : State → ℝ := fun x =>
    Real.exp (-(∑ j : Fin 2, beta j * D.momentMap x j))
  let a : State → ℝ := fun x =>
    -(∑ j : Fin 2, v j * D.momentMap x j)
  have hline :
      (fun t => souriauMassieu D (betaLine beta v t)) =
        (fun t => logSumExp w a t) := by
    ext t
    unfold souriauMassieu betaLine logSumExp logSumExpPartition
      realGibbsPartition realGibbsKernel realPairingEnergy w a
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    ring
  rw [hline]
  have hw : ∀ x, 0 < w x := fun x => Real.exp_pos _
  rw [logSumExp_secondDeriv_eq_variance w a hw]
  rw [logSumExpVariance_eq_centered w a hw 0]
  unfold logSumExpWeight
  have hpart : logSumExpPartition w a 0 = realGibbsPartition D beta := by
    unfold logSumExpPartition realGibbsPartition w a realGibbsKernel
      realPairingEnergy
    apply Finset.sum_congr rfl
    intro x _
    rw [zero_mul, Real.exp_zero, mul_one]
  have hweight : ∀ x : State,
      w x * Real.exp (0 * a x) / realGibbsPartition D beta =
        realGibbsWeight D beta x := by
    intro x
    rw [zero_mul, Real.exp_zero, mul_one]
    rfl
  have hmean :
      (∑ x : State, realGibbsWeight D beta x * a x) =
        -(∑ i : Fin 2, v i * souriauChargeMean D beta i) := by
    unfold a souriauChargeMean
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_assoc, mul_comm, mul_left_comm]
  simp_rw [hpart]
  simp_rw [hweight, hmean]
  unfold fisherSouriauQuadratic fisherSouriauMatrix
  calc
    ∑ x : State,
        realGibbsWeight D beta x *
          (a x - (-(∑ i : Fin 2, v i * souriauChargeMean D beta i))) ^ (2 : ℕ)
        = ∑ x : State, realGibbsWeight D beta x *
          (∑ i : Fin 2, v i *
            (D.momentMap x i - souriauChargeMean D beta i)) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro x _
      have hcenter :
          a x - (-(∑ i : Fin 2, v i * souriauChargeMean D beta i)) =
            -(∑ i : Fin 2, v i *
              (D.momentMap x i - souriauChargeMean D beta i)) := by
        unfold a
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      rw [hcenter]
      ring
    _ = fisherSouriauQuadratic D beta v :=
      (fisherSouriauQuadratic_eq_directionalVariance D beta v).symm

theorem souriauMassieu_directionalSecondDeriv_nonneg
    (beta v : Fin 2 → ℝ) :
    0 ≤ deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaLine beta v t')) t) 0 := by
  rw [souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic D beta v]
  exact fisherSouriauQuadratic_nonneg D beta v

theorem souriauMassieu_directionalSecondDeriv_pos_of_nonzero_direction
    (beta v : Fin 2 → ℝ)
    (h : ∃ x : State,
      (∑ i : Fin 2, v i *
        (D.momentMap x i - souriauChargeMean D beta i)) ≠ 0) :
    0 < deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaLine beta v t')) t) 0 := by
  rw [souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic D beta v]
  exact fisherSouriauQuadratic_pos_of_nonzero_direction D beta v h

end InfoGeometry.Lie
