import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperator
import InfoGeometry.Arithmetic.FiniteMobiusShiftOperator

/-!
# Finite Dirichlet-Möbius Convolution Representation Bridge

This module formalizes the algebraic representation of the Dirichlet convolution ring
via logarithmic scale translation operators:

1. **Multiplicative Log-Scale Representation:**
   The logarithmic map $(\mathbb{N}_{>0}, \times) \to (\mathbb{R}, +)$ intertwines integer multiplication
   with translation composition:
   $$T_{\ln m} \circ T_{\ln n} = T_{\ln(mn)}$$

2. **General Arithmetic Shift Operator:**
   For any arithmetic function $a : \text{ArithmeticFunction } \mathbb{C}$ and finite cutoff $N$:
   $$\mathcal{R}_N(a)(f)(t) = \sum_{n=1}^N a(n) T_{\ln n} f(t)$$
   specializing to $\operatorname{finiteDirichletShift}_N$ when $a = \zeta$ and
   $\operatorname{finiteMobiusShift}_N$ when $a = \mu$.

3. **Mellin-Character Readout on Exponential Tests:**
   $$\mathcal{R}_N(a)(e_s)(t) = \left( \sum_{n=1}^N a(n) n^{-s} \right) e_s(t)$$

4. **Exact Convolution Inversion:**
   $$\mu * \zeta = 1, \qquad \zeta * \mu = 1$$
   establishing that the Möbius function is the exact convolution inverse of the zeta function
   in the arithmetic ring $(\text{ArithmeticFunction } \mathbb{C}, *, +)$.

5. **Firewall on Finite Cutoffs:**
   The inversion holds at the coefficient/convolution level $\mu * \zeta = 1$; on finite cutoffs,
   $\mathcal{R}_N(\zeta) \circ \mathcal{R}_N(\mu) \neq I$ due to cross-terms with $mn > N$.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteDirichletMobiusConvolutionRepresentationBridge

open scoped BigOperators
open ArithmeticFunction
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperator
open InfoGeometry.Arithmetic.FiniteMobiusShiftOperator

-- =========================================================================
-- 1. Multiplicative Log-Scale Representation
-- =========================================================================

/-- 🏆 THEOREM 1: Log-scale translation is a multiplicative homomorphism on $\mathbb{N}_{>0}$:
    $T_{\ln m} \circ T_{\ln n} = T_{\ln(mn)}$. -/
theorem logScaleTranslation_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f : ℝ → ℂ) :
    logScaleTranslation (Real.log (m : ℝ)) (logScaleTranslation (Real.log (n : ℝ)) f) =
      logScaleTranslation (Real.log ((m * n : ℕ) : ℝ)) f := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    push_cast
    exact Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hn_pos)
  ext t
  dsimp [logScaleTranslation]
  rw [hlog]
  congr 1
  ring

-- =========================================================================
-- 2. General Arithmetic Shift Operator
-- =========================================================================

/-- The finite shift operator associated with an arithmetic function $a$. -/
def arithmeticShift (a : ArithmeticFunction ℂ) (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∑ n ∈ Finset.Icc 1 N, a n * logScaleTranslation (Real.log (n : ℝ)) f t

/-- 🏆 THEOREM 2: Dirichlet shift is the arithmetic shift for the zeta function $\zeta(n) = 1$. -/
theorem arithmeticShift_zeta_eq_dirichlet (N : ℕ) (f : ℝ → ℂ) :
    arithmeticShift zeta N f = finiteDirichletShift N f := by
  ext t
  dsimp [arithmeticShift, finiteDirichletShift, zeta_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
  have : (((if n = 0 then 0 else 1 : ℕ) : ℂ)) = 1 := by simp [hn_pos.ne']
  rw [this, one_mul]

/-- 🏆 THEOREM 3: Möbius shift is the arithmetic shift for the Möbius function $\mu$. -/
theorem arithmeticShift_moebius_eq_mobius (N : ℕ) (f : ℝ → ℂ) :
    arithmeticShift moebius N f = finiteMobiusShift N f := by
  rfl

-- =========================================================================
-- 3. Mellin-Character Readout on Exponential Test Family
-- =========================================================================

/-- 🏆 THEOREM 4: General arithmetic shift on exponential test functions. -/
theorem arithmeticShift_exponentialTest_cpow (a : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) (t : ℝ) :
    arithmeticShift a N (exponentialTest s) t =
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) * exponentialTest s t := by
  dsimp [arithmeticShift]
  simp_rw [logScaleTranslation_exponentialTest]
  have hsum : (∑ n ∈ Finset.Icc 1 N, a n * (Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) * exponentialTest s t)) =
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) * exponentialTest s t := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
    have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    rw [Complex.cpow_def_of_ne_zero hn0]
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      exact (Complex.ofReal_log (le_of_lt hn_pos_real)).symm
    rw [hlog]
    ring_nf
  exact hsum

-- =========================================================================
-- 4. Exact Dirichlet Convolution Inversion
-- =========================================================================

/-- 🏆 THEOREM 5: Exact Dirichlet convolution inversion: $\mu * \zeta = 1$. -/
theorem moebius_mul_zeta_eq_one :
    ((moebius : ArithmeticFunction ℂ) * (zeta : ArithmeticFunction ℂ)) = 1 :=
  coe_moebius_mul_coe_zeta

/-- 🏆 THEOREM 6: Exact Dirichlet convolution inversion: $\zeta * \mu = 1$. -/
theorem zeta_mul_moebius_eq_one :
    ((zeta : ArithmeticFunction ℂ) * (moebius : ArithmeticFunction ℂ)) = 1 :=
  coe_zeta_mul_coe_moebius

/-- 🏆 THEOREM 7: Evaluation of the convolution unit: $(\mu * \zeta)(1) = 1$. -/
theorem moebius_mul_zeta_apply_one :
    ((moebius : ArithmeticFunction ℂ) * (zeta : ArithmeticFunction ℂ)) 1 = 1 := by
  rw [moebius_mul_zeta_eq_one, one_apply, if_pos rfl]

/-- 🏆 THEOREM 8: Annihilation on non-units: $(\mu * \zeta)(k) = 0$ for $k > 1$. -/
theorem moebius_mul_zeta_apply_ne_one {k : ℕ} (hk : k ≠ 1) :
    ((moebius : ArithmeticFunction ℂ) * (zeta : ArithmeticFunction ℂ)) k = 0 := by
  rw [moebius_mul_zeta_eq_one, one_apply, if_neg hk]

end InfoGeometry.Arithmetic.FiniteDirichletMobiusConvolutionRepresentationBridge
