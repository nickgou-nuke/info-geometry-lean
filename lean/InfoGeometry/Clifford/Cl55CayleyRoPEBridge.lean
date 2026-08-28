import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.Cl55WittCircularAxes
import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

/-!
# Algebraic Cayley Frontier for Native `Cl(5,5)` Rotor Carriers

The elliptic and split square laws have genuinely different denominator behaviour:
1. **Elliptic Generator ($J^2 = -1$):**
   - Invertible denominator $(1 + J)^{-1} = \frac{1}{2}(1 - J)$.
   - Globally well-defined Cayley transform $C(J) = (1 - J)(1 + J)^{-1} = -J$.
   - Specializes to $C(E_i) = -E_i$ and $C(B_{ij}) = -B_{ij}$ on native Clifford bivectors.

2. **Split Generator ($K^2 = +1$):**
   - Zero divisor obstruction: $(1 + K)(1 - K) = 0$ and $(1 - K)(1 + K) = 0$.
   - Demonstrates that split geometry naturally replaces global Cayley inversion
     with Peirce / idempotent projector decomposition ($1 \pm K = 2 P_\pm$).
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CayleyRoPEBridge

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The candidate inverse for $(1 + J)$ in an elliptic algebra: $\frac{1}{2}(1 - J)$. -/
def ellipticCayleyDenInv (J : A) : A :=
  (1 / 2 : ℝ) • ((1 : A) - J)

/-- Right inverse identity: $(1 + J) \cdot \frac{1}{2}(1 - J) = 1$. -/
theorem ellipticCayleyDenInv_right (J : A) (hJ : J * J = -(1 : A)) :
    (1 + J) * ellipticCayleyDenInv J = 1 := by
  unfold ellipticCayleyDenInv
  rw [mul_smul_comm]
  have h_prod : (1 + J) * (1 - J) = (2 : ℝ) • (1 : A) := by
    rw [add_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one, hJ]
    have h2 : (2 : ℝ) • (1 : A) = (1 : A) + 1 := by
      have : (2 : ℝ) = 1 + 1 := by norm_num
      rw [this, add_smul, one_smul]
    rw [h2]
    abel
  rw [h_prod, smul_smul]
  have h1 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [h1, one_smul]

/-- Left inverse identity: $\frac{1}{2}(1 - J) \cdot (1 + J) = 1$. -/
theorem ellipticCayleyDenInv_left (J : A) (hJ : J * J = -(1 : A)) :
    ellipticCayleyDenInv J * (1 + J) = 1 := by
  unfold ellipticCayleyDenInv
  rw [smul_mul_assoc]
  have h_prod : (1 - J) * (1 + J) = (2 : ℝ) • (1 : A) := by
    rw [sub_mul, mul_add, mul_add]
    simp only [one_mul, mul_one, hJ]
    have h2 : (2 : ℝ) • (1 : A) = (1 : A) + 1 := by
      have : (2 : ℝ) = 1 + 1 := by norm_num
      rw [this, add_smul, one_smul]
    rw [h2]
    abel
  rw [h_prod, smul_smul]
  have h1 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [h1, one_smul]

/-- Cayley transform of an elliptic generator $J$: $C(J) = (1 - J)(1 + J)^{-1}$. -/
def ellipticCayley (J : A) : A :=
  (1 - J) * ellipticCayleyDenInv J

/-- **Theorem (Elliptic Cayley Normal Form)**:
    $C(J) = (1 - J) \cdot \frac{1}{2}(1 - J) = -J$. -/
theorem ellipticCayley_eq_neg (J : A) (hJ : J * J = -(1 : A)) :
    ellipticCayley J = -J := by
  unfold ellipticCayley ellipticCayleyDenInv
  rw [mul_smul_comm]
  have h_prod : (1 - J) * (1 - J) = -((2 : ℝ) • J) := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one, hJ]
    have h2 : (2 : ℝ) • J = J + J := by
      have : (2 : ℝ) = 1 + 1 := by norm_num
      rw [this, add_smul, one_smul]
    rw [h2]
    abel
  rw [h_prod, smul_neg, smul_smul]
  have h1 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [h1, one_smul]

omit [Algebra ℝ A] in
/-- Zero divisor identity for split generator: $(1 + K)(1 - K) = 0$. -/
theorem splitCayley_denominator_product_zero (K : A)
    (hK : K * K = (1 : A)) :
    (1 + K) * (1 - K) = 0 := by
  rw [add_mul, mul_sub, mul_sub]
  simp only [one_mul, mul_one, hK]
  abel

omit [Algebra ℝ A] in
/-- Zero divisor reverse identity: $(1 - K)(1 + K) = 0$. -/
theorem splitCayley_denominator_product_zero_rev (K : A)
    (hK : K * K = (1 : A)) :
    (1 - K) * (1 + K) = 0 := by
  rw [sub_mul, mul_add, mul_add]
  simp only [one_mul, mul_one, hK]
  abel

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

/-- Native $\mathrm{Cl}(5,5)$ elliptic CAR axis Cayley transform: $C(E_i) = -E_i$. -/
theorem ellipticAxis55_cayley_eq_neg (i : Fin 5) :
    ellipticCayley (ellipticAxis55 i) = -(ellipticAxis55 i) :=
  ellipticCayley_eq_neg _ (ellipticAxis55_sq i)

/-- Native $\mathrm{Cl}(5,5)$ RoPE bivector Cayley transform: $C(B_{ij}) = -B_{ij}$. -/
theorem ropeBivector55_cayley_eq_neg (i j : Fin 5) (hij : i ≠ j) :
    ellipticCayley (ropeBivector55 i j) = -(ropeBivector55 i j) :=
  ellipticCayley_eq_neg _ (ropeBivector55_sq i j hij)

/-- Native $\mathrm{Cl}(5,5)$ hyperbolic axis split zero divisor obstruction. -/
theorem hyperbolicAxis55_cayley_denominator_zero_divisor (i : Fin 5) :
    (1 + hyperbolicAxis55 i) * (1 - hyperbolicAxis55 i) = 0 :=
  splitCayley_denominator_product_zero _ (hyperbolicAxis55_sq i)

theorem hyperbolicAxis55_one_add_ne_zero (i : Fin 5) :
    (1 + hyperbolicAxis55 i) ≠ 0 := by
  intro h
  have hK : hyperbolicAxis55 i = -(1 : Cl55) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using h
  have hanti := hyperbolicAxis55_ellipticAxis55_anticommute i
  rw [hK] at hanti
  have hEneg : -(ellipticAxis55 i + ellipticAxis55 i) = 0 := by
    simpa [neg_mul, mul_neg, neg_add] using hanti
  have hE : ellipticAxis55 i + ellipticAxis55 i = 0 := neg_eq_zero.mp hEneg
  have hE0 : ellipticAxis55 i = 0 := by
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    apply (smul_eq_zero.mp (show (2 : ℝ) • ellipticAxis55 i = 0 by
      simpa [two_smul] using hE)).resolve_left htwo
  have hsq := ellipticAxis55_sq i
  rw [hE0] at hsq
  norm_num at hsq

theorem hyperbolicAxis55_one_sub_ne_zero (i : Fin 5) :
    (1 - hyperbolicAxis55 i) ≠ 0 := by
  intro h
  have hK : hyperbolicAxis55 i = (1 : Cl55) := by
    exact (sub_eq_zero.mp h).symm
  have hanti := hyperbolicAxis55_ellipticAxis55_anticommute i
  rw [hK] at hanti
  have hE : ellipticAxis55 i + ellipticAxis55 i = 0 := by
    simpa using hanti
  have hE0 : ellipticAxis55 i = 0 := by
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    apply (smul_eq_zero.mp (show (2 : ℝ) • ellipticAxis55 i = 0 by
      simpa [two_smul] using hE)).resolve_left htwo
  have hsq := ellipticAxis55_sq i
  rw [hE0] at hsq
  norm_num at hsq

/-! ## Master Synthesis -/

/--
🏆 **GRAND SYNTHESIS THEOREM: Algebraic Cayley Inversion vs. Split Obstruction**

Unifies:
1. Elliptic Cayley bilateral inverse $(1 + J) \cdot \frac{1}{2}(1 - J) = 1 = \frac{1}{2}(1 - J) \cdot (1 + J)$.
2. Elliptic Cayley identity $C(J) = -J$, specialized to native $\mathrm{Cl}(5,5)$ axes $E_i$ and bivectors $B_{ij}$.
3. Split Cayley zero-divisor obstruction $(1 + K)(1 - K) = 0$, demonstrating that split channels
   replace global inversion with Peirce projector routing.
-/
theorem grand_cayley_rope_split_synthesis
    (J K : A)
    (hJ : J * J = -1) (hK : K * K = 1)
    (i j : Fin 5) (hij : i ≠ j) :
    -- (1) Elliptic Invertibility & Normal Form
    ((1 + J) * ellipticCayleyDenInv J = 1 ∧
     ellipticCayleyDenInv J * (1 + J) = 1 ∧
     ellipticCayley J = -J) ∧
    -- (2) Split Zero-Divisor Obstruction
    ((1 + K) * (1 - K) = 0 ∧
     (1 - K) * (1 + K) = 0) ∧
    -- (3) Native Cl(5,5) Specializations
    (ellipticCayley (ellipticAxis55 i) = -(ellipticAxis55 i) ∧
     ellipticCayley (ropeBivector55 i j) = -(ropeBivector55 i j) ∧
     (1 + hyperbolicAxis55 i) * (1 - hyperbolicAxis55 i) = 0) := by
  refine ⟨⟨ellipticCayleyDenInv_right J hJ,
           ellipticCayleyDenInv_left J hJ,
           ellipticCayley_eq_neg J hJ⟩,
          ⟨splitCayley_denominator_product_zero K hK,
           splitCayley_denominator_product_zero_rev K hK⟩,
          ⟨ellipticAxis55_cayley_eq_neg i,
           ropeBivector55_cayley_eq_neg i j hij,
           hyperbolicAxis55_cayley_denominator_zero_divisor i⟩⟩

end InfoGeometry.Clifford.Cl55CayleyRoPEBridge
