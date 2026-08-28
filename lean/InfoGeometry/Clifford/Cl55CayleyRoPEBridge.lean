import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

/-! Algebraic Cayley frontier for the native `Cl(5,5)` rotor carriers.

The elliptic and split square laws have genuinely different denominator
behaviour.  This file records only those finite ring identities; it does not
introduce a KZ connection, holonomy, or analytic exponential.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CayleyRoPEBridge

variable {A : Type*} [Ring A] [Algebra ℝ A]

def ellipticCayleyDenInv (J : A) : A :=
  (1 / 2 : ℝ) • ((1 : A) - J)

theorem ellipticCayleyDenInv_right (J : A) (hJ : J * J = -(1 : A)) :
    (1 + J) * ellipticCayleyDenInv J = 1 := by
  unfold ellipticCayleyDenInv
  calc
    (1 + J) * ((1 / 2 : ℝ) • (1 - J)) =
        (1 / 2 : ℝ) • ((1 + J) * (1 - J)) := by rw [mul_smul_comm]
    _ = 1 := by
      simp only [mul_sub, add_mul, mul_one, one_mul]
      rw [hJ]
      module

theorem ellipticCayleyDenInv_left (J : A) (hJ : J * J = -(1 : A)) :
    ellipticCayleyDenInv J * (1 + J) = 1 := by
  unfold ellipticCayleyDenInv
  calc
    (1 / 2 : ℝ) • ((1 - J) * (1 + J)) =
        (1 / 2 : ℝ) • (1 - J * J) := by
      noncomm_ring
    _ = 1 := by rw [hJ]; module

def ellipticCayley (J : A) : A :=
  (1 - J) * ellipticCayleyDenInv J

theorem ellipticCayley_eq_neg (J : A) (hJ : J * J = -(1 : A)) :
    ellipticCayley J = -J := by
  unfold ellipticCayley ellipticCayleyDenInv
  rw [mul_smul_comm]
  simp only [sub_mul, mul_one, mul_neg]
  rw [hJ]
  module

theorem splitCayley_denominator_product_zero (K : A)
    (hK : K * K = (1 : A)) :
    (1 + K) * (1 - K) = 0 := by
  simp only [add_mul, mul_sub, mul_one, one_mul]
  rw [hK]
  module

theorem splitCayley_denominator_product_zero_rev (K : A)
    (hK : K * K = (1 : A)) :
    (1 - K) * (1 + K) = 0 := by
  simp only [sub_mul, mul_add, mul_one, one_mul]
  rw [hK]
  module

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

theorem ellipticAxis55_cayley_eq_neg (i : Fin 5) :
    ellipticCayley (ellipticAxis55 i) = -(ellipticAxis55 i) := by
  exact ellipticCayley_eq_neg _ (ellipticAxis55_sq i)

theorem ropeBivector55_cayley_eq_neg (i j : Fin 5) (hij : i ≠ j) :
    ellipticCayley (ropeBivector55 i j) = -(ropeBivector55 i j) := by
  exact ellipticCayley_eq_neg _ (ropeBivector55_sq i j hij)

theorem hyperbolicAxis55_cayley_denominator_zero_divisor (i : Fin 5) :
    (1 + hyperbolicAxis55 i) * (1 - hyperbolicAxis55 i) = 0 := by
  exact splitCayley_denominator_product_zero _ (hyperbolicAxis55_sq i)

end InfoGeometry.Clifford.Cl55CayleyRoPEBridge
