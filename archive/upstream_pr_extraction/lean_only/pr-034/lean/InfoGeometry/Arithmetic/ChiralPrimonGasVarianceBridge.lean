import InfoGeometry.Arithmetic.ChiralPrimonGas

/-!
# Finite fermionic variance positivity

This consumer exposes the elementary probability bounds hidden in the
fermionic occupation definition.  It is a finite theorem only: no zeta
limit, Fisher-Hessian asymptotic, or thermodynamic completion is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ChiralPrimonGasVarianceBridge

open InfoGeometry.Arithmetic.ChiralPrimonGas

theorem primeEnergy_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ primeEnergy p := by
  unfold primeEnergy
  apply Real.log_nonneg
  exact_mod_cast hp.one_le

theorem primeEnergy_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < primeEnergy p := by
  unfold primeEnergy
  apply Real.log_pos
  exact_mod_cast hp.one_lt

theorem occupation_fermion_lt_one (beta nu : ℝ) (p : ℕ) :
    occupation Statistics.fermion beta nu p < 1 := by
  unfold occupation
  by_cases hx : 0 ≤ beta * primeEnergy p - nu
  · simp [hx]
    have hy : 0 < Real.exp (nu - beta * primeEnergy p) := Real.exp_pos _
    have hden : 0 < 1 + Real.exp (nu - beta * primeEnergy p) := by
      positivity
    apply (div_lt_iff₀ hden).2
    linarith
  · simp [hx]
    have hy : 0 < Real.exp (beta * primeEnergy p - nu) := Real.exp_pos _
    have hden : 0 < 1 + Real.exp (beta * primeEnergy p - nu) := by
      positivity
    have h : 1 / (1 + Real.exp (beta * primeEnergy p - nu)) < 1 := by
      apply (div_lt_iff₀ hden).2
      linarith
    simpa only [one_div] using h

theorem localNumberVariance_fermion_nonneg (beta nu : ℝ) (p : ℕ) :
    0 ≤ localNumberVariance Statistics.fermion beta nu p := by
  unfold localNumberVariance
  exact mul_nonneg
    (occupation_fermion_nonneg beta nu p)
    (sub_nonneg.mpr (le_of_lt (occupation_fermion_lt_one beta nu p)))

theorem localNumberVariance_fermion_pos (beta nu : ℝ) (p : ℕ) :
    0 < localNumberVariance Statistics.fermion beta nu p := by
  unfold localNumberVariance
  exact mul_pos
    (occupation_fermion_pos beta nu p)
    (sub_pos.mpr (occupation_fermion_lt_one beta nu p))

theorem localNumberVariance_fermion_le_quarter (beta nu : ℝ) (p : ℕ) :
    localNumberVariance Statistics.fermion beta nu p ≤ (1 / 4 : ℝ) := by
  unfold localNumberVariance
  have hn : 0 ≤ occupation Statistics.fermion beta nu p :=
    occupation_fermion_nonneg beta nu p
  have hlt : occupation Statistics.fermion beta nu p < 1 :=
    occupation_fermion_lt_one beta nu p
  nlinarith [sq_nonneg (occupation Statistics.fermion beta nu p - (1 / 2 : ℝ))]

theorem localEnergyVariance_fermion_nonneg (beta nu : ℝ) (p : ℕ) :
    0 ≤ localEnergyVariance Statistics.fermion beta nu p := by
  unfold localEnergyVariance
  exact mul_nonneg
    (mul_self_nonneg (primeEnergy p))
    (localNumberVariance_fermion_nonneg beta nu p)

theorem localEnergyNumberCovariance_fermion_nonneg
    {p : ℕ} (hp : Nat.Prime p) (beta nu : ℝ) :
    0 ≤ localEnergyNumberCovariance Statistics.fermion beta nu p := by
  unfold localEnergyNumberCovariance
  exact mul_nonneg (primeEnergy_nonneg_of_prime hp)
    (localNumberVariance_fermion_nonneg beta nu p)

theorem sector_varNumber_nonneg_of_fermion
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu : ℝ) :
    0 ≤ (sector G beta nu).varNumber := by
  simp only [sector, hG]
  exact Finset.sum_nonneg (fun p _ =>
    localNumberVariance_fermion_nonneg beta nu p)

theorem sector_varEnergy_nonneg_of_fermion
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu : ℝ) :
    0 ≤ (sector G beta nu).varEnergy := by
  simp only [sector, hG]
  exact Finset.sum_nonneg (fun p _ =>
    localEnergyVariance_fermion_nonneg beta nu p)

theorem sector_covEnergyNumber_nonneg_of_fermion
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu : ℝ) :
    0 ≤ (sector G beta nu).covEnergyNumber := by
  simp only [sector, hG]
  exact Finset.sum_nonneg (fun p hp =>
    localEnergyNumberCovariance_fermion_nonneg
      (G.register.property p hp) beta nu)

/-- The local covariance quadratic form is a square weighted by the local
fermionic variance. -/
def localCovarianceQuadratic (beta nu a b : ℝ) (p : ℕ) : ℝ :=
  localNumberVariance Statistics.fermion beta nu p *
    (a * primeEnergy p + b) ^ 2

theorem localCovarianceQuadratic_nonneg (beta nu a b : ℝ) (p : ℕ) :
    0 ≤ localCovarianceQuadratic beta nu a b p := by
  change 0 ≤ localNumberVariance Statistics.fermion beta nu p *
    (a * primeEnergy p + b) ^ 2
  exact mul_nonneg (localNumberVariance_fermion_nonneg beta nu p) (sq_nonneg _)

/-- The full finite fermionic `(E,N)` covariance block is positive
semidefinite, expressed by its quadratic form. -/
theorem sector_covariance_quadratic_nonneg_of_fermion
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu a b : ℝ) :
    0 ≤
      a ^ 2 * (sector G beta nu).varEnergy +
      2 * a * b * (sector G beta nu).covEnergyNumber +
      b ^ 2 * (sector G beta nu).varNumber := by
  simp only [sector, hG]
  have h_sum :
      a ^ 2 * Finset.sum G.register.primes (fun p => localEnergyVariance Statistics.fermion beta nu p) +
      2 * a * b * Finset.sum G.register.primes (fun p => localEnergyNumberCovariance Statistics.fermion beta nu p) +
      b ^ 2 * Finset.sum G.register.primes (fun p => localNumberVariance Statistics.fermion beta nu p) =
      Finset.sum G.register.primes (fun p => localCovarianceQuadratic beta nu a b p) := by
    dsimp [localCovarianceQuadratic, localEnergyVariance, localEnergyNumberCovariance]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [h_sum]
  exact Finset.sum_nonneg (fun p _ => localCovarianceQuadratic_nonneg beta nu a b p)

/-- The determinant of the finite `(E,N)` covariance block is nonnegative. -/
theorem sector_covariance_determinant_nonneg_of_fermion
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu : ℝ) :
    0 ≤
      (sector G beta nu).varEnergy * (sector G beta nu).varNumber -
        (sector G beta nu).covEnergyNumber ^ 2 := by
  let ve := (sector G beta nu).varEnergy
  let vn := (sector G beta nu).varNumber
  let c := (sector G beta nu).covEnergyNumber
  have h₁ := sector_covariance_quadratic_nonneg_of_fermion
    G hG beta nu vn (-c)
  have h₂ := sector_covariance_quadratic_nonneg_of_fermion
    G hG beta nu c (-ve)
  have hve : 0 ≤ ve := sector_varEnergy_nonneg_of_fermion G hG beta nu
  have hvn : 0 ≤ vn := sector_varNumber_nonneg_of_fermion G hG beta nu
  have h₃ := sector_covariance_quadratic_nonneg_of_fermion G hG beta nu 1 1
  have h₄ := sector_covariance_quadratic_nonneg_of_fermion G hG beta nu 1 (-1)
  dsimp [ve, vn, c] at h₁ h₂ h₃ h₄ hve hvn ⊢
  by_cases hve' : 0 < (sector G beta nu).varEnergy
  · nlinarith [sq_nonneg ((sector G beta nu).varEnergy *
      (sector G beta nu).varNumber -
      (sector G beta nu).covEnergyNumber ^ 2)]
  · have hve0 : (sector G beta nu).varEnergy = 0 := le_antisymm (not_lt.mp hve') hve
    by_cases hvn' : 0 < (sector G beta nu).varNumber
    · have h₅ := sector_covariance_quadratic_nonneg_of_fermion
        G hG beta nu (-(sector G beta nu).covEnergyNumber) 1
      nlinarith [sq_nonneg (sector G beta nu).covEnergyNumber]
    · have hvn0 : (sector G beta nu).varNumber = 0 :=
        le_antisymm (not_lt.mp hvn') hvn
      nlinarith [sq_nonneg (sector G beta nu).covEnergyNumber]

end InfoGeometry.Arithmetic.ChiralPrimonGasVarianceBridge
