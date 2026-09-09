import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

/-!
# Centered BKM covariance on the native faithful finite density carrier

This owner isolates the algebraic target of the concrete Gibbs Hessian theorem.
It introduces no second density carrier and no supplied derivative law.

For a faithful density `D`, write

`E_D[A] = Re Tr(D.rho * A)`

and center an observable by

`A° = A - E_D[A] • 1`.

The existing Kubo--Mori pairing is already a genuine interval integral of
`rho^s A* rho^(1-s) B`.  The theorems below prove that pairing with the
identity recovers the expectation and that the BKM form on centered
observables is exactly the ordinary BKM response minus the product of first
moments.

This is deliberately an algebraic covariance owner.  It does not assert that
the covariance is the second derivative of a Gibbs log-partition function;
that remaining equality requires differentiating the two-point numerator in a
noncommuting direction.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance

open SouriauOnsagerBKM
open scoped Interval

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/-- Real expectation readout of an operator in a faithful finite state. -/
def expectationReal {n : ℕ}
    (D : FaithfulDensityOperator n) (A : Operator n) : ℝ :=
  (finiteOperatorTrace (D.rho * A)).re

/-- Centered sufficient statistic `A - E_D[A] 1`. -/
def centeredStatistic {n : ℕ}
    (D : FaithfulDensityOperator n) (A : Operator n) : Operator n :=
  A - expectationReal D A • (1 : Operator n)

/-- Pointwise Kubo--Mori insertion of the identity is the ordinary first
moment, independently of the interpolation parameter. -/
theorem kuboMoriIntegrand_one_left
    {n : ℕ} (D : FaithfulDensityOperator n)
    (B : Operator n) (s : ℝ) :
    D.kuboMoriIntegrand (1 : Operator n) B s =
      finiteOperatorTrace (D.rho * B) := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  simp only [star_one, mul_one]
  rw [← D.rpow_add]
  have hs : s + (1 - s) = 1 := by ring
  rw [hs, D.rpow_one]

/-- Integrated identity insertion equals the ordinary first moment. -/
theorem kuboMoriPairing_one_left
    {n : ℕ} (D : FaithfulDensityOperator n)
    (B : Operator n) :
    D.kuboMoriPairing (1 : Operator n) B =
      finiteOperatorTrace (D.rho * B) := by
  unfold FaithfulDensityOperator.kuboMoriPairing
  simp_rw [kuboMoriIntegrand_one_left]
  simp

/-- Real BKM pairing with the identity is the real expectation. -/
theorem bkmRealBilinForm_one_left
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (B : Operator n) :
    D.bkmRealBilinForm hpow (1 : Operator n) B =
      expectationReal D B := by
  rw [D.bkmRealBilinForm_apply, kuboMoriPairing_one_left]
  rfl

/-- By Onsager symmetry, identity insertion on the right gives the same real
expectation. -/
theorem bkmRealBilinForm_one_right
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A : Operator n) :
    D.bkmRealBilinForm hpow A (1 : Operator n) =
      expectationReal D A := by
  calc
    D.bkmRealBilinForm hpow A (1 : Operator n) =
        D.bkmRealBilinForm hpow (1 : Operator n) A :=
      (D.bkmRealBilinForm_symm hpow).eq A (1 : Operator n)
    _ = expectationReal D A := bkmRealBilinForm_one_left D hpow A

/-- The normalized identity has unit real BKM norm. -/
theorem bkmRealBilinForm_one_one
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) :
    D.bkmRealBilinForm hpow (1 : Operator n) (1 : Operator n) = 1 := by
  rw [bkmRealBilinForm_one_left D hpow (1 : Operator n)]
  change (finiteOperatorTrace (D.rho * (1 : Operator n))).re = 1
  rw [mul_one, D.trace_one]
  norm_num

/-- A centered statistic has zero expectation. -/
theorem expectationReal_centeredStatistic
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A : Operator n) :
    expectationReal D (centeredStatistic D A) = 0 := by
  rw [← bkmRealBilinForm_one_left D hpow]
  unfold centeredStatistic
  simp only [map_sub, map_smul]
  rw [bkmRealBilinForm_one_left, bkmRealBilinForm_one_one]
  simp

/-- Native centered BKM covariance. -/
def centeredBKMRealCovariance {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : Operator n) : ℝ :=
  D.bkmRealBilinForm hpow (centeredStatistic D A) (centeredStatistic D B)

/-- Centering subtracts exactly the product of first moments:

`Cov_BKM(A,B) = g_BKM(A,B) - E[A] E[B]`.
-/
theorem centeredBKMRealCovariance_eq
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A B : Operator n) :
    centeredBKMRealCovariance D hpow A B =
      D.bkmRealBilinForm hpow A B -
        expectationReal D A * expectationReal D B := by
  unfold centeredBKMRealCovariance centeredStatistic
  rw [(D.bkmRealBilinForm hpow).map_sub]
  rw [(D.bkmRealBilinForm hpow).map_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [(D.bkmRealBilinForm hpow A).map_sub]
  rw [(D.bkmRealBilinForm hpow A).map_smul]
  rw [(D.bkmRealBilinForm hpow (1 : Operator n)).map_sub]
  rw [(D.bkmRealBilinForm hpow (1 : Operator n)).map_smul]
  rw [bkmRealBilinForm_one_left,
    bkmRealBilinForm_one_right,
    bkmRealBilinForm_one_one]
  simp [smul_eq_mul]
  ring

/-- The centered covariance is symmetric. -/
theorem centeredBKMRealCovariance_symm
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A B : Operator n) :
    centeredBKMRealCovariance D hpow A B =
      centeredBKMRealCovariance D hpow B A := by
  rw [centeredBKMRealCovariance_eq, centeredBKMRealCovariance_eq]
  rw [(D.bkmRealBilinForm_symm hpow).eq]
  ring

/-- The diagonal centered covariance is the BKM response of the centered
fluctuation itself. -/
theorem centeredBKMRealCovariance_self
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A : Operator n) :
    centeredBKMRealCovariance D hpow A A =
      D.bkmRealBilinForm hpow (centeredStatistic D A) (centeredStatistic D A) :=
  rfl

end InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
