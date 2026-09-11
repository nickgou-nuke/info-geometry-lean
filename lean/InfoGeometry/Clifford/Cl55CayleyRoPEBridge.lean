import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cayley bridge for elliptic RoPE and split obstruction

For a native elliptic Cl55 generator `J` with `J^2 = -1`, the Cayley
 denominator `1 + J` is explicitly invertible with inverse `(1/2)(1-J)`.
The corresponding Cayley transform `(1-J)(1+J)^{-1}` simplifies to `-J`.

For a native split generator `K` with `K^2 = +1`, the factors `1+K` and
`1-K` multiply to zero.  Thus the same global Cayley denominator is not
silently treated as invertible in the split channel.

This file proves only these Clifford identities.  It does not identify the
Cayley element with a KZ/RoPE monodromy intertwiner without a separate typed
comparison datum and intertwining theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

/-- Explicit inverse candidate for `1 + J` when `J^2 = -1`. -/
def ellipticCayleyDenInv (J : Cl55) : Cl55 :=
  (1 / 2 : ℝ) • ((1 : Cl55) - J)

/-- If `J^2 = -1`, the explicit candidate is a right inverse of `1+J`. -/
theorem ellipticCayleyDenInv_right
    (J : Cl55) (hJ : J * J = -(1 : Cl55)) :
    ((1 : Cl55) + J) * ellipticCayleyDenInv J = 1 := by
  unfold ellipticCayleyDenInv
  rw [mul_smul_comm]
  calc
    (1 / 2 : ℝ) • (((1 : Cl55) + J) * ((1 : Cl55) - J)) =
        (1 / 2 : ℝ) • ((1 : Cl55) - J * J) := by rw [show
          ((1 : Cl55) + J) * ((1 : Cl55) - J) = (1 : Cl55) - J * J by
            noncomm_ring]
    _ = (1 / 2 : ℝ) • (2 • (1 : Cl55)) := by rw [hJ]; module
    _ = 1 := by module

/-- If `J^2 = -1`, the explicit candidate is also a left inverse of `1+J`. -/
theorem ellipticCayleyDenInv_left
    (J : Cl55) (hJ : J * J = -(1 : Cl55)) :
    ellipticCayleyDenInv J * ((1 : Cl55) + J) = 1 := by
  unfold ellipticCayleyDenInv
  rw [smul_mul_assoc]
  calc
    (1 / 2 : ℝ) • (((1 : Cl55) - J) * ((1 : Cl55) + J)) =
        (1 / 2 : ℝ) • ((1 : Cl55) - J * J) := by rw [show
          ((1 : Cl55) - J) * ((1 : Cl55) + J) = (1 : Cl55) - J * J by
            noncomm_ring]
    _ = (1 / 2 : ℝ) • (2 • (1 : Cl55)) := by rw [hJ]; module
    _ = 1 := by module

/-- Native Cayley transform with the explicit elliptic denominator inverse. -/
def ellipticCayley (J : Cl55) : Cl55 :=
  ((1 : Cl55) - J) * ellipticCayleyDenInv J

/-- For every square-minus-one generator, the Cayley transform collapses to
`-J` in the real Clifford algebra. -/
theorem ellipticCayley_eq_neg
    (J : Cl55) (hJ : J * J = -(1 : Cl55)) :
    ellipticCayley J = -J := by
  unfold ellipticCayley ellipticCayleyDenInv
  rw [mul_smul_comm]
  calc
    (1 / 2 : ℝ) • (((1 : Cl55) - J) * ((1 : Cl55) - J)) =
        (1 / 2 : ℝ) • ((1 : Cl55) - 2 • J + J * J) := by rw [show
          ((1 : Cl55) - J) * ((1 : Cl55) - J) =
            (1 : Cl55) - 2 • J + J * J by noncomm_ring]
    _ = (1 / 2 : ℝ) • (-2 • J) := by rw [hJ]; module
    _ = -J := by module

/-- Specialization to the native elliptic CAR axis. -/
theorem ellipticAxis55_cayley_eq_neg (i : Fin 5) :
    ellipticCayley (ellipticAxis55 i) = -ellipticAxis55 i := by
  exact ellipticCayley_eq_neg (ellipticAxis55 i) (ellipticAxis55_sq i)

/-- Specialization to the genuine RoPE bivector from two distinct split axes. -/
theorem ropeBivector55_cayley_eq_neg
    {i j : Fin 5} (hij : i ≠ j) :
    ellipticCayley (ropeBivector55 i j) = -ropeBivector55 i j := by
  exact ellipticCayley_eq_neg (ropeBivector55 i j) (ropeBivector55_sq i j hij)

/-- For `K^2=1`, the two Cayley factors multiply to zero.
Neither factor is asserted nonzero: `K = 1` and `K = -1` are allowed. -/
theorem split_cayley_denominator_product_zero
    (K : Cl55) (hK : K * K = (1 : Cl55)) :
    ((1 : Cl55) + K) * ((1 : Cl55) - K) = 0 := by
  calc
    ((1 : Cl55) + K) * ((1 : Cl55) - K) =
        (1 : Cl55) - K * K := by noncomm_ring
    _ = 0 := by rw [hK]; simp

/-- The reversed split product vanishes as well. -/
theorem split_cayley_denominator_product_zero_rev
    (K : Cl55) (hK : K * K = (1 : Cl55)) :
    ((1 : Cl55) - K) * ((1 : Cl55) + K) = 0 := by
  calc
    ((1 : Cl55) - K) * ((1 : Cl55) + K) =
        (1 : Cl55) - K * K := by noncomm_ring
    _ = 0 := by rw [hK]; simp

/-- Native hyperbolic-axis specialization of the split Cayley obstruction. -/
theorem hyperbolicAxis55_cayley_denominator_zero_divisor (i : Fin 5) :
    ((1 : Cl55) + hyperbolicAxis55 i) *
      ((1 : Cl55) - hyperbolicAxis55 i) = 0 := by
  exact split_cayley_denominator_product_zero
    (hyperbolicAxis55 i) (hyperbolicAxis55_sq i)

end InfoGeometry.Clifford.Clifford55
