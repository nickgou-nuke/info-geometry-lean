import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Noncommutative derivatives of operator powers

This file exposes the native Mathlib derivative of the power map on a
possibly noncommutative normed algebra.  It is the finite-stage owner needed
for the Duhamel derivative of the Banach-algebra exponential.

No commutativity, diagonalization, trace, or scalar readout is used.
-/

namespace InfoGeometry.OperatorAlgebra

open scoped RightActions

variable {𝕜 A : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A]

/--
The Fréchet derivative of the `n`th power at `a`.

Applied to a tangent operator `h`, this is the noncommutative insertion sum
`∑ i ∈ range n, a ^ i * h * a ^ (n.pred - i)`.
-/
noncomputable def powerDerivative (n : ℕ) (a : A) : A →L[𝕜] A :=
  ∑ i ∈ Finset.range n,
    MulOpposite.op (a ^ i) •
      a ^ (n.pred - i) •
        ContinuousLinearMap.id 𝕜 A

/--
The power map has the noncommutative insertion derivative.  This is Mathlib's
native theorem `hasFDerivAt_pow'`, exposed under an owner-level name for the
operator-algebraic Duhamel development.
-/
theorem hasFDerivAt_power_noncommutative (n : ℕ) (a : A) :
    HasFDerivAt (fun x : A => x ^ n)
      (powerDerivative (𝕜 := 𝕜) n a) a := by
  exact hasFDerivAt_pow' n

/-- The derivative of the constant zeroth power is zero. -/
@[simp]
theorem powerDerivative_zero (a : A) :
    powerDerivative (𝕜 := 𝕜) 0 a = 0 := by
  simp [powerDerivative]

/-- The derivative of the identity first power is the identity map. -/
@[simp]
theorem powerDerivative_one (a : A) :
    powerDerivative 1 a = ContinuousLinearMap.id 𝕜 A := by
  simp [powerDerivative]

/--
The `n`th summand in the Banach-algebra exponential series.
-/
noncomputable def exponentialTerm (n : ℕ) (a : A) : A :=
  ((n.factorial : 𝕜)⁻¹) • a ^ n

/--
The derivative of the `n`th exponential-series summand.  The factorial
coefficient is scalar, while the derivative retains the full noncommutative
left/right insertion order.
-/
noncomputable def exponentialTermDerivative (n : ℕ) (a : A) : A →L[𝕜] A :=
  ((n.factorial : 𝕜)⁻¹) • powerDerivative n a

/--
Each exponential-series summand has the factorial-weighted noncommutative
power derivative.
-/
theorem hasFDerivAt_exponentialTerm (n : ℕ) (a : A) :
    HasFDerivAt (exponentialTerm (𝕜 := 𝕜) n)
      (exponentialTermDerivative (𝕜 := 𝕜) n a) a := by
  simpa [exponentialTerm, exponentialTermDerivative] using
    (hasFDerivAt_power_noncommutative (𝕜 := 𝕜) n a).const_smul
      ((n.factorial : 𝕜)⁻¹)

/--
Termwise differentiation of the noncommutative exponential series.

The hypotheses are exactly the convergence obligations required by Mathlib's
`hasFDerivAt_tsum`: a summable derivative majorant and convergence at one
base point.  They are explicit theorem propertys, not fields hidden in an
evidence record.
-/
theorem hasFDerivAt_exponentialSeries_of_bound
    [IsRCLikeNormedField 𝕜] [CompleteSpace A]
    (u : ℕ → ℝ)
    (hu : Summable u)
    (hbound :
      ∀ (n : ℕ) (a : A),
        ‖exponentialTermDerivative (𝕜 := 𝕜) n a‖ ≤ u n)
    (hbase :
      Summable (fun n : ℕ =>
        exponentialTerm (𝕜 := 𝕜) n (0 : A)))
    (a : A) :
    HasFDerivAt
      (fun x : A => ∑' n : ℕ, exponentialTerm (𝕜 := 𝕜) n x)
      (∑' n : ℕ, exponentialTermDerivative (𝕜 := 𝕜) n a)
      a := by
  exact hasFDerivAt_tsum hu
    (fun n x => hasFDerivAt_exponentialTerm (𝕜 := 𝕜) n x)
    hbound hbase a

/--
The canonical noncommutative Fréchet derivative of the Banach-algebra
exponential at `a`, obtained by changing the origin of Mathlib's exponential
formal multilinear series.
-/
noncomputable def exponentialDerivative (a : A) : A →L[𝕜] A :=
  (continuousMultilinearCurryFin1 𝕜 A A)
    ((NormedSpace.expSeries 𝕜 A).changeOrigin a 1)

/--
The Banach-algebra exponential has the changed-origin power-series derivative
at every point.  Unlike Mathlib's commutative simplification
`HasFDerivAt.exp`, this statement retains the full noncommutative derivative.
-/
theorem hasFDerivAt_exp_noncommutative
    [CharZero 𝕜] [ContinuousSMul ℚ 𝕜] [CompleteSpace A]
    (a : A) :
    HasFDerivAt NormedSpace.exp
      (exponentialDerivative (𝕜 := 𝕜) a) a := by
  simpa [exponentialDerivative] using
    (NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := 𝕜) (𝔸 := A)).hasFDerivAt
      (y := a) (by simp)

end InfoGeometry.OperatorAlgebra
