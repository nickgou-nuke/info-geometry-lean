import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# InfoGeometry.Arithmetic.PrimitiveSetsAbove

Lean owner surface for the primitive-set problem with weight `1 / (n log n)`.

This module does not claim the analytic proof. It formalizes:

- the primitive-set predicate,
- the weighted finite and infinite sums,
- support-above-`x` conditions,
- faithful theorem statements for the finite and infinite forms,
- basic divisibility lemmas needed by the eventual chain/Markov argument.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic

/-- The arithmetic weight `1 / (n log n)`, extended by `0` on `n ≤ 1`. -/
def primitiveWeight (n : ℕ) : ℝ :=
  if 1 < n then 1 / ((n : ℝ) * Real.log n) else 0

/--
Mellin/Laplace kernel for the primitive weight.

For `n > 1` this is `exp (-s log n) = n^(-s)`. We keep the kernel at `0` on
`n ≤ 1` so that the integral bridge matches `primitiveWeight` without side
conditions.
-/
def primitiveMellinKernel (n : ℕ) (s : ℝ) : ℝ :=
  if 1 < n then Real.exp (-s * Real.log n) else 0

/-- Inverted spectral base attached to `n`, viewed as `a ↦ a⁻¹`. -/
def primitiveInverseBase (n : ℕ) : ℝ :=
  ((n : ℝ) : ℝ)⁻¹

/--
Shifted modular-time kernel.

This is the same Mellin kernel after the translation `s = τ + 1`, so the
improper integral runs over `τ ∈ (0, ∞)`.
-/
def primitiveModularKernel (n : ℕ) (τ : ℝ) : ℝ :=
  primitiveMellinKernel n (τ + 1)

/--
A primitive subset of the natural numbers: inside the set, divisibility only
occurs on equal elements.
-/
def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b

/-- Finite primitive-set specialization. -/
def PrimitiveFinset (A : Finset ℕ) : Prop :=
  PrimitiveSet (A : Set ℕ)

/-- A set is supported above `x` if every member is at least `x`. -/
def SupportedAbove (x : ℕ) (A : Set ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ∈ A → x ≤ n

/-- Finite support-above-`x` specialization. -/
def SupportedAboveFinset (x : ℕ) (A : Finset ℕ) : Prop :=
  SupportedAbove x (A : Set ℕ)

/-- Finite primitive-set weighted sum. -/
def primitiveWeightSum (A : Finset ℕ) : ℝ :=
  Finset.sum A primitiveWeight

/--
Unnormalized arithmetic weight attached to a finite count profile.

This is the commutative arithmetic shadow of an unnormalized modular weight:
the raw count at `n` multiplied by the Mellin/modular kernel `e^{-s log n}`.
-/
def arithmeticCountWeight (counts : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  counts n * primitiveMellinKernel n s

/-- Total mass of a finite count profile over a chosen support. -/
def arithmeticTotalMass (A : Finset ℕ) (counts : ℕ → ℝ) : ℝ :=
  Finset.sum A counts

/--
Normalized base shape of a finite count profile, when viewed projectively.

This is the scale-free ray representative obtained by dividing by the total
mass on the chosen finite support.
-/
def arithmeticBaseShape (A : Finset ℕ) (counts : ℕ → ℝ) (n : ℕ) : ℝ :=
  counts n / arithmeticTotalMass A counts

/-- Arithmetic partition readout of a finite count profile. -/
def arithmeticPartition (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ) : ℝ :=
  Finset.sum A (arithmeticCountWeight counts s)

/--
Shape-side Mellin readout obtained by evaluating the kernel against the
projectively normalized base shape.
-/
def arithmeticShapeMellin (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ) : ℝ :=
  Finset.sum A (fun n => arithmeticBaseShape A counts n * primitiveMellinKernel n s)

/--
Real-valued von Mangoldt weight on `ℕ`, exposed locally on this owner surface.

This is a thin arithmetic alias to Mathlib's `ArithmeticFunction.vonMangoldt`,
kept here so the primitive-set Dirichlet lane can stay scalar-valued.
-/
def realVonMangoldt (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/--
Prime-weighted Mellin/Dirichlet readout over a finite support.

This is the finite-support shadow of the logarithmic derivative lane associated
to `-ζ'/ζ`.
-/
def arithmeticPrimePartition (A : Finset ℕ) (s : ℝ) : ℝ :=
  Finset.sum A (fun n => realVonMangoldt n * primitiveMellinKernel n s)

/-- The indicator series used for infinite primitive sets. -/
def primitiveIndicatorSeries (A : Set ℕ) : ℕ → ℝ :=
  by
    classical
    exact fun n => if n ∈ A then primitiveWeight n else 0

/--
Finite formulation of the primitive-sets-above problem.

This is the clean finitary approximation one would prove first before passing
to infinite primitive subsets by exhaustion.
-/
def PrimitiveSetsAboveFiniteStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x₀ : ℕ, ∀ ⦃x : ℕ⦄, x₀ ≤ x →
      ∀ A : Finset ℕ, PrimitiveFinset A → SupportedAboveFinset x A →
        primitiveWeightSum A ≤ 1 + ε

/--
Infinite formulation of the primitive-sets-above problem using `tsum`.

The summability hypothesis is explicit, so the theorem surface does not hide
any analytic convergence obligations.
-/
def PrimitiveSetsAboveInfiniteStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x₀ : ℕ, ∀ ⦃x : ℕ⦄, x₀ ≤ x →
      ∀ A : Set ℕ, PrimitiveSet A → SupportedAbove x A →
        Summable (primitiveIndicatorSeries A) →
        tsum (primitiveIndicatorSeries A) ≤ 1 + ε

/--
Big-`O(1 / log x)` version of the infinite primitive-set statement.

This matches the shape of the theorem in the user-provided note.
-/
def PrimitiveSetsAboveBigOBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ ⦃x : ℕ⦄, 2 ≤ x →
      ∀ A : Set ℕ, PrimitiveSet A → SupportedAbove x A →
        Summable (primitiveIndicatorSeries A) →
        tsum (primitiveIndicatorSeries A) ≤ 1 + C / Real.log x

theorem primitiveWeight_eq_zero_of_not_lt_two {n : ℕ} (h : ¬ 1 < n) :
    primitiveWeight n = 0 := by
  simp [primitiveWeight, h]

theorem primitiveWeight_eq_zero_of_le_one {n : ℕ} (h : n ≤ 1) :
    primitiveWeight n = 0 := by
  exact primitiveWeight_eq_zero_of_not_lt_two (not_lt.mpr h)

theorem primitiveMellinKernel_eq_zero_of_not_lt_two {n : ℕ} (h : ¬ 1 < n) :
    primitiveMellinKernel n = fun _ => 0 := by
  funext s
  simp [primitiveMellinKernel, h]

theorem primitiveMellinKernel_eq_zero_of_le_one {n : ℕ} (h : n ≤ 1) :
    primitiveMellinKernel n = fun _ => 0 :=
  primitiveMellinKernel_eq_zero_of_not_lt_two (not_lt.mpr h)

theorem primitiveMellinKernel_eq_exp_neg_mul_log {n : ℕ} (h : 1 < n) :
    primitiveMellinKernel n = fun s => Real.exp (-s * Real.log n) := by
  funext s
  simp [primitiveMellinKernel, h]

theorem primitiveMellinKernel_nonneg (n : ℕ) (s : ℝ) :
    0 ≤ primitiveMellinKernel n s := by
  by_cases h : 1 < n
  · rw [primitiveMellinKernel_eq_exp_neg_mul_log h]
    positivity
  · simp [primitiveMellinKernel, h]

theorem realVonMangoldt_eq_if_isPrimePow (n : ℕ) :
    realVonMangoldt n = if IsPrimePow n then Real.log (Nat.minFac n) else 0 := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_apply (n := n)

theorem realVonMangoldt_one :
    realVonMangoldt 1 = 0 := by
  simp [realVonMangoldt]

theorem realVonMangoldt_nonneg (n : ℕ) :
    0 ≤ realVonMangoldt n := by
  rw [realVonMangoldt]
  exact ArithmeticFunction.vonMangoldt_nonneg (n := n)

theorem realVonMangoldt_eq_zero_iff (n : ℕ) :
    realVonMangoldt n = 0 ↔ ¬ IsPrimePow n := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_eq_zero_iff (n := n)

theorem realVonMangoldt_ne_zero_iff (n : ℕ) :
    realVonMangoldt n ≠ 0 ↔ IsPrimePow n := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_ne_zero_iff (n := n)

theorem realVonMangoldt_pos_iff (n : ℕ) :
    0 < realVonMangoldt n ↔ IsPrimePow n := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_pos_iff (n := n)

theorem realVonMangoldt_apply_pow (n k : ℕ) (hk : k ≠ 0) :
    realVonMangoldt (n ^ k) = realVonMangoldt n := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_apply_pow (n := n) (k := k) hk

theorem realVonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) :
    realVonMangoldt p = Real.log p := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_apply_prime hp

theorem sum_realVonMangoldt_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, realVonMangoldt d = Real.log (n : ℝ) := by
  simpa [realVonMangoldt] using ArithmeticFunction.vonMangoldt_sum (n := n)

theorem primitiveInverseBase_pos {n : ℕ} (h : 1 < n) :
    0 < primitiveInverseBase n := by
  unfold primitiveInverseBase
  positivity

theorem log_primitiveInverseBase {n : ℕ} (h : 1 < n) :
    Real.log (primitiveInverseBase n) = -Real.log (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast lt_trans Nat.zero_lt_one h
  simp [primitiveInverseBase, Real.log_inv]

theorem primitiveMellinKernel_eq_exp_mul_log_inverseBase {n : ℕ} (h : 1 < n) :
    primitiveMellinKernel n = fun s => Real.exp (s * Real.log (primitiveInverseBase n)) := by
  funext s
  rw [primitiveMellinKernel_eq_exp_neg_mul_log h]
  rw [log_primitiveInverseBase h]
  ring_nf

theorem primitiveModularKernel_eq_mellinKernel_shift (n : ℕ) :
    primitiveModularKernel n = fun τ => primitiveMellinKernel n (τ + 1) := by
  rfl

theorem primitiveModularKernel_eq_exp_neg_shifted_log {n : ℕ} (h : 1 < n) :
    primitiveModularKernel n = fun τ => Real.exp (-(τ + 1) * Real.log n) := by
  funext τ
  simp [primitiveModularKernel, primitiveMellinKernel, h]

theorem primitiveModularKernel_eq_exp_mul_log_inverseBase {n : ℕ} (h : 1 < n) :
    primitiveModularKernel n = fun τ => Real.exp ((τ + 1) * Real.log (primitiveInverseBase n)) := by
  funext τ
  rw [primitiveModularKernel_eq_exp_neg_shifted_log h]
  rw [log_primitiveInverseBase h]
  ring_nf

theorem primitiveWeight_nonneg (n : ℕ) : 0 ≤ primitiveWeight n := by
  by_cases h : 1 < n
  · have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast lt_trans Nat.zero_lt_one h
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast h)
    have hdenom_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hn_pos hlog_pos
    have hweight_pos : 0 < 1 / ((n : ℝ) * Real.log (n : ℝ)) := one_div_pos.mpr hdenom_pos
    simpa [primitiveWeight, h] using hweight_pos.le
  · simp [primitiveWeight, h]

theorem primitiveWeight_pos {n : ℕ} (h : 1 < n) :
    0 < primitiveWeight n := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast lt_trans Nat.zero_lt_one h
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast h)
  have hdenom_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hn_pos hlog_pos
  have hweight_pos : 0 < 1 / ((n : ℝ) * Real.log (n : ℝ)) := one_div_pos.mpr hdenom_pos
  simpa [primitiveWeight, h] using hweight_pos

theorem primitiveWeight_eq_integral_mellinKernel (n : ℕ) :
    primitiveWeight n = ∫ s : ℝ in Set.Ioi 1, primitiveMellinKernel n s := by
  by_cases h : 1 < n
  · have hlog_pos : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast h)
    have hneg : -Real.log (n : ℝ) < 0 := by linarith
    rw [primitiveWeight, if_pos h, primitiveMellinKernel_eq_exp_neg_mul_log h]
    have hrewrite :
        (∫ s : ℝ in Set.Ioi 1, Real.exp (-s * Real.log (n : ℝ)))
          =
        ∫ s : ℝ in Set.Ioi 1, Real.exp ((-Real.log (n : ℝ)) * s) := by
      congr with s
      ring_nf
    rw [hrewrite]
    rw [integral_exp_mul_Ioi hneg 1]
    have hlog_ne : Real.log (n : ℝ) ≠ 0 := hlog_pos.ne'
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast lt_trans Nat.zero_lt_one h
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    calc
      1 / ((n : ℝ) * Real.log (n : ℝ))
          = ((n : ℝ)⁻¹) / Real.log (n : ℝ) := by
              field_simp [hn_ne, hlog_ne]
      _ = Real.exp (-Real.log (n : ℝ)) / Real.log (n : ℝ) := by
            rw [Real.exp_neg, Real.exp_log hn_pos]
      _ = -Real.exp (-Real.log (n : ℝ)) / (-Real.log (n : ℝ)) := by
            field_simp [hlog_ne]
      _ = -Real.exp ((-Real.log (n : ℝ)) * 1) / (-Real.log (n : ℝ)) := by
            ring_nf
  · have hkernel_zero := primitiveMellinKernel_eq_zero_of_not_lt_two h
    rw [primitiveWeight_eq_zero_of_not_lt_two h, hkernel_zero]
    simp

theorem primitiveWeight_eq_integral_modularKernel (n : ℕ) :
    primitiveWeight n = ∫ τ : ℝ in Set.Ioi 0, primitiveModularKernel n τ := by
  by_cases h : 1 < n
  · rw [primitiveWeight, if_pos h, primitiveModularKernel_eq_exp_neg_shifted_log h]
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast h)
    have hneg : -Real.log (n : ℝ) < 0 := by linarith
    have hsplit :
        (fun τ : ℝ => Real.exp (-(τ + 1) * Real.log (n : ℝ)))
          =
        fun τ : ℝ => Real.exp (-Real.log (n : ℝ)) * Real.exp ((-Real.log (n : ℝ)) * τ) := by
      funext τ
      rw [show -(τ + 1) * Real.log (n : ℝ) = (-Real.log (n : ℝ)) + ((-Real.log (n : ℝ)) * τ) by ring]
      rw [Real.exp_add]
    rw [hsplit, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hneg 0]
    have hlog_ne : Real.log (n : ℝ) ≠ 0 := hlog_pos.ne'
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast lt_trans Nat.zero_lt_one h
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    calc
      1 / ((n : ℝ) * Real.log (n : ℝ))
          = ((n : ℝ)⁻¹) / Real.log (n : ℝ) := by
              field_simp [hn_ne, hlog_ne]
      _ = Real.exp (-Real.log (n : ℝ)) / Real.log (n : ℝ) := by
            rw [Real.exp_neg, Real.exp_log hn_pos]
      _ = Real.exp (-Real.log (n : ℝ)) * (-Real.exp ((-Real.log (n : ℝ)) * 0) / (-Real.log (n : ℝ))) := by
            simp
            field_simp [hlog_ne]
  · rw [primitiveWeight_eq_zero_of_not_lt_two h]
    simp [primitiveModularKernel, primitiveMellinKernel, h]

theorem primitiveWeightSum_nonneg (A : Finset ℕ) :
    0 ≤ primitiveWeightSum A := by
  unfold primitiveWeightSum
  refine Finset.sum_nonneg ?_
  intro n hn
  exact primitiveWeight_nonneg n

theorem primitiveWeightSum_empty :
    primitiveWeightSum ∅ = 0 := by
  simp [primitiveWeightSum]

theorem primitiveWeightSum_singleton (n : ℕ) :
    primitiveWeightSum ({n} : Finset ℕ) = primitiveWeight n := by
  simp [primitiveWeightSum]

theorem arithmeticCountWeight_eq_mul_kernel (counts : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    arithmeticCountWeight counts s n = counts n * primitiveMellinKernel n s := by
  rfl

theorem arithmeticPartition_eq_sum (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ) :
    arithmeticPartition A counts s = Finset.sum A (fun n => counts n * primitiveMellinKernel n s) := by
  rfl

theorem arithmeticTotalMass_eq_sum (A : Finset ℕ) (counts : ℕ → ℝ) :
    arithmeticTotalMass A counts = Finset.sum A counts := by
  rfl

theorem arithmeticBaseShape_eq_div (A : Finset ℕ) (counts : ℕ → ℝ) (n : ℕ) :
    arithmeticBaseShape A counts n = counts n / arithmeticTotalMass A counts := by
  rfl

theorem arithmeticShapeMellin_eq_sum (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ) :
    arithmeticShapeMellin A counts s
      = Finset.sum A (fun n => arithmeticBaseShape A counts n * primitiveMellinKernel n s) := by
  rfl

theorem arithmeticPartition_empty (counts : ℕ → ℝ) (s : ℝ) :
    arithmeticPartition ∅ counts s = 0 := by
  simp [arithmeticPartition]

theorem arithmeticTotalMass_empty (counts : ℕ → ℝ) :
    arithmeticTotalMass ∅ counts = 0 := by
  simp [arithmeticTotalMass]

theorem arithmeticShapeMellin_empty (counts : ℕ → ℝ) (s : ℝ) :
    arithmeticShapeMellin ∅ counts s = 0 := by
  simp [arithmeticShapeMellin]

theorem arithmeticPrimePartition_eq_sum (A : Finset ℕ) (s : ℝ) :
    arithmeticPrimePartition A s
      = Finset.sum A (fun n => realVonMangoldt n * primitiveMellinKernel n s) := by
  rfl

theorem arithmeticPrimePartition_empty (s : ℝ) :
    arithmeticPrimePartition ∅ s = 0 := by
  simp [arithmeticPrimePartition]

theorem arithmeticPrimePartition_nonneg (A : Finset ℕ) (s : ℝ) :
    0 ≤ arithmeticPrimePartition A s := by
  unfold arithmeticPrimePartition
  refine Finset.sum_nonneg ?_
  intro n hn
  exact mul_nonneg (realVonMangoldt_nonneg n) (primitiveMellinKernel_nonneg n s)

theorem arithmeticPartition_nonneg
    (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ)
    (hcounts : ∀ ⦃n : ℕ⦄, n ∈ A → 0 ≤ counts n) :
    0 ≤ arithmeticPartition A counts s := by
  unfold arithmeticPartition arithmeticCountWeight
  refine Finset.sum_nonneg ?_
  intro n hn
  exact mul_nonneg (hcounts hn) (by exact primitiveMellinKernel_nonneg n s)

theorem arithmeticTotalMass_nonneg
    (A : Finset ℕ) (counts : ℕ → ℝ)
    (hcounts : ∀ ⦃n : ℕ⦄, n ∈ A → 0 ≤ counts n) :
    0 ≤ arithmeticTotalMass A counts := by
  unfold arithmeticTotalMass
  refine Finset.sum_nonneg ?_
  intro n hn
  exact hcounts hn

theorem arithmeticPartition_eq_totalMass_mul_shapeMellin
    (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ)
    (hmass : arithmeticTotalMass A counts ≠ 0) :
    arithmeticPartition A counts s
      = arithmeticTotalMass A counts * arithmeticShapeMellin A counts s := by
  unfold arithmeticPartition arithmeticShapeMellin arithmeticBaseShape arithmeticCountWeight
  calc
    Finset.sum A (fun n => counts n * primitiveMellinKernel n s)
        = Finset.sum A (fun n =>
            (arithmeticTotalMass A counts * (counts n / arithmeticTotalMass A counts))
              * primitiveMellinKernel n s) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              field_simp [hmass]
    _ = Finset.sum A (fun n =>
          arithmeticTotalMass A counts
            * ((counts n / arithmeticTotalMass A counts) * primitiveMellinKernel n s)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring
    _ = arithmeticTotalMass A counts
          * Finset.sum A (fun n =>
              (counts n / arithmeticTotalMass A counts) * primitiveMellinKernel n s) := by
          rw [Finset.mul_sum]

theorem arithmeticLogPartition_eq_log_totalMass_add_log_shapeMellin
    (A : Finset ℕ) (counts : ℕ → ℝ) (s : ℝ)
    (hmass : 0 < arithmeticTotalMass A counts)
    (hshape : 0 < arithmeticShapeMellin A counts s) :
    Real.log (arithmeticPartition A counts s)
      = Real.log (arithmeticTotalMass A counts) + Real.log (arithmeticShapeMellin A counts s) := by
  rw [arithmeticPartition_eq_totalMass_mul_shapeMellin A counts s hmass.ne']
  rw [Real.log_mul hmass.ne' hshape.ne']

theorem primitiveWeightSum_eq_integral_mellinKernel (A : Finset ℕ) :
    primitiveWeightSum A = ∫ s : ℝ in Set.Ioi 1, Finset.sum A (fun n => primitiveMellinKernel n s) := by
  calc
    primitiveWeightSum A
        = Finset.sum A (fun n => ∫ s : ℝ in Set.Ioi 1, primitiveMellinKernel n s) := by
            simp [primitiveWeightSum, primitiveWeight_eq_integral_mellinKernel]
    _ = ∫ s : ℝ in Set.Ioi 1, Finset.sum A (fun n => primitiveMellinKernel n s) := by
          symm
          refine MeasureTheory.integral_finset_sum A ?_
          intro n hn
          by_cases h : 1 < n
          · have hlog_pos : 0 < Real.log (n : ℝ) := by
              exact Real.log_pos (by exact_mod_cast h)
            have hneg : -Real.log (n : ℝ) < 0 := by linarith
            have hk :
                MeasureTheory.Integrable
                  (fun x : ℝ => Real.exp (-(Real.log (n : ℝ) * x)))
                  (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
              simpa [MeasureTheory.IntegrableOn] using (integrableOn_exp_mul_Ioi hneg 1)
            have hEq :
                (fun x : ℝ => Real.exp (-(Real.log (n : ℝ) * x)))
                  =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 1)] primitiveMellinKernel n := by
              filter_upwards with x
              simp [primitiveMellinKernel, h, mul_comm]
            exact hk.congr hEq
          · have hz :
                MeasureTheory.Integrable (fun _ : ℝ => (0 : ℝ))
                  (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
                MeasureTheory.integrable_zero (α := ℝ) (ε' := ℝ)
                  (μ := MeasureTheory.volume.restrict (Set.Ioi 1))
            have hEq :
                (fun _ : ℝ => (0 : ℝ))
                  =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 1)] primitiveMellinKernel n := by
              filter_upwards with x
              simp [primitiveMellinKernel, h]
            exact hz.congr hEq

/--
Expand the finite von-Mangoldt weighted primitive sum as a sum over the sigma of
elements and their divisors.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_eq
    (A : Finset ℕ) :
    Finset.sum A (fun a => primitiveWeight a * Finset.sum a.divisors realVonMangoldt)
      =
    Finset.sum (A.sigma fun a => a.divisors) (fun x => primitiveWeight x.1 * realVonMangoldt x.2) := by
  classical
  calc
    Finset.sum A (fun a => primitiveWeight a * Finset.sum a.divisors realVonMangoldt)
        = Finset.sum A (fun a => Finset.sum a.divisors (fun d => primitiveWeight a * realVonMangoldt d)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.mul_sum]
    _ = Finset.sum (A.sigma fun a => a.divisors) (fun x => primitiveWeight x.1 * realVonMangoldt x.2) := by
          rw [Finset.sum_sigma']

/--
Replace the inner divisor sum against `realVonMangoldt` by the logarithm using
the classical divisor identity `∑_{d | n} Λ(d) = log n`.
-/
theorem primitiveWeight_vonMangoldt_divisorSum_eq_log
    (A : Finset ℕ) :
    Finset.sum A (fun a => primitiveWeight a * Finset.sum a.divisors realVonMangoldt)
      =
    Finset.sum A (fun a => primitiveWeight a * Real.log a) := by
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [sum_realVonMangoldt_divisors]

theorem primitiveFinset_empty :
    PrimitiveFinset ∅ := by
  intro a b ha
  simp at ha

theorem primitiveFinset_singleton (n : ℕ) :
    PrimitiveFinset ({n} : Finset ℕ) := by
  intro a b ha hb hab
  have ha' : a = n := by simpa using ha
  have hb' : b = n := by simpa using hb
  rw [ha', hb']

theorem PrimitiveSet.eq_of_dvd {A : Set ℕ} (hA : PrimitiveSet A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ∣ b) :
    a = b :=
  hA ha hb hab

theorem PrimitiveSet.dvd_antisymm_on {A : Set ℕ} (hA : PrimitiveSet A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ∣ b) (_hba : b ∣ a) :
    a = b := by
  exact PrimitiveSet.eq_of_dvd hA ha hb hab

theorem PrimitiveSet.not_dvd_of_ne {A : Set ℕ} (hA : PrimitiveSet A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
    ¬ a ∣ b := by
  intro hab
  exact hne (PrimitiveSet.eq_of_dvd hA ha hb hab)

theorem PrimitiveSet.not_lt_of_dvd {A : Set ℕ} (hA : PrimitiveSet A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ∣ b) :
    ¬ a < b := by
  intro hlt
  exact hlt.ne (PrimitiveSet.eq_of_dvd hA ha hb hab)

theorem PrimitiveFinset.eq_of_dvd {A : Finset ℕ} (hA : PrimitiveFinset A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ∣ b) :
    a = b :=
  PrimitiveSet.eq_of_dvd hA ha hb hab

theorem PrimitiveFinset.not_dvd_of_ne {A : Finset ℕ} (hA : PrimitiveFinset A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
    ¬ a ∣ b :=
  PrimitiveSet.not_dvd_of_ne hA ha hb hne

/--
Quotient support of a finite set by a fixed divisor `d`: keep the elements
divisible by `d` and divide them by `d`.
-/
def primitiveDivisorQuotient (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (A.filter fun a => d ∣ a).image fun a => a / d

/-- The fixed-`d` divisor fiber inside a finite support. -/
def primitiveDivisorFiber (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  A.filter fun a => d ∣ a

/--
If every element of a primitive finite set is divisible by `d`, then dividing
the whole support by `d` preserves primitiveness.
-/
theorem primitiveFinset_image_div
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ} (hd0 : d ≠ 0)
    (hdiv : ∀ ⦃a : ℕ⦄, a ∈ A → d ∣ a) :
    PrimitiveFinset (A.image fun a => a / d) := by
  intro x y hx hy hxy
  rcases Finset.mem_image.mp hx with ⟨a, haA, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨b, hbA, rfl⟩
  have hda : d ∣ a := hdiv haA
  have hdb : d ∣ b := hdiv hbA
  have hab : a ∣ b := by
    rcases hxy with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      b = d * (b / d) := by rw [Nat.mul_div_cancel' hdb]
      _ = d * (a / d * k) := by rw [hk]
      _ = a * k := by rw [← Nat.mul_assoc, Nat.mul_div_cancel' hda]
  have hab_eq : a = b := PrimitiveFinset.eq_of_dvd hA haA hbA hab
  rw [← Nat.mul_right_inj hd0]
  rw [Nat.mul_div_cancel' hda, Nat.mul_div_cancel' hdb, hab_eq]

theorem primitiveDivisorQuotient_primitive
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ} (hd0 : d ≠ 0) :
    PrimitiveFinset (primitiveDivisorQuotient A d) := by
  apply primitiveFinset_image_div
  · intro a b ha hb hab
    exact hA (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  · exact hd0
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

theorem primitiveDivisorQuotient_supportedAbove
    {A : Finset ℕ} {x d : ℕ} (hA : SupportedAboveFinset x A) :
    SupportedAboveFinset (x / d) (primitiveDivisorQuotient A d) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
  have haA : a ∈ A := (Finset.mem_filter.mp ha).1
  exact Nat.div_le_div_right (hA haA)

theorem primitiveDivisorFiber_eq_filter (A : Finset ℕ) (d : ℕ) :
    primitiveDivisorFiber A d = A.filter (fun a => d ∣ a) := by
  rfl

theorem primitiveDivisorQuotient_eq_image_fiber (A : Finset ℕ) (d : ℕ) :
    primitiveDivisorQuotient A d = (primitiveDivisorFiber A d).image (fun a => a / d) := by
  rfl

theorem primitiveDivisorFiber_dvd {A : Finset ℕ} {d a : ℕ}
    (ha : a ∈ primitiveDivisorFiber A d) :
    d ∣ a := by
  exact (Finset.mem_filter.mp ha).2

theorem primitiveDivisorFiber_mem {A : Finset ℕ} {d a : ℕ}
    (ha : a ∈ primitiveDivisorFiber A d) :
    a ∈ A := by
  exact (Finset.mem_filter.mp ha).1

theorem primitiveDivisorFiber_div_injective
    {A : Finset ℕ} {d : ℕ} :
    Set.InjOn (fun a : ℕ => a / d) (primitiveDivisorFiber A d) := by
  intro a ha b hb hab
  have hda : d ∣ a := primitiveDivisorFiber_dvd ha
  have hdb : d ∣ b := primitiveDivisorFiber_dvd hb
  calc
    a = d * (a / d) := by rw [Nat.mul_div_cancel' hda]
    _ = d * (b / d) := by rw [show a / d = b / d from hab]
    _ = b := by rw [Nat.mul_div_cancel' hdb]

/--
Reindex a fixed divisor fiber by dividing through by `d`. This transports a sum
over the `d`-divisible part of `A` to a sum over the quotient support.
-/
theorem sum_primitiveDivisorFiber_eq_sum_primitiveDivisorQuotient
    (A : Finset ℕ) {d : ℕ} (f : ℕ → ℝ) :
    Finset.sum (primitiveDivisorFiber A d) f
      = Finset.sum (primitiveDivisorQuotient A d)
          (fun m => f (d * m)) := by
  rw [primitiveDivisorQuotient_eq_image_fiber]
  rw [Finset.sum_image (primitiveDivisorFiber_div_injective (A := A))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hda : d ∣ a := primitiveDivisorFiber_dvd ha
  rw [Nat.mul_div_cancel' hda]

/--
Specialization of the fixed-divisor reindexing to the primitive weight.
-/
theorem primitiveWeightSum_primitiveDivisorQuotient_eq
    (A : Finset ℕ) (d : ℕ) :
    primitiveWeightSum (primitiveDivisorQuotient A d)
      = Finset.sum (primitiveDivisorFiber A d) (fun a => primitiveWeight (a / d)) := by
  unfold primitiveWeightSum
  rw [primitiveDivisorQuotient_eq_image_fiber]
  rw [Finset.sum_image (primitiveDivisorFiber_div_injective (A := A) (d := d))]

/--
Reindex the fixed-`d` divisor fiber against the primitive weight viewed on the
quotient support.
-/
theorem sum_primitiveDivisorFiber_primitiveWeight_mul_eq
    (A : Finset ℕ) (d : ℕ) :
    Finset.sum (primitiveDivisorFiber A d) (fun a => primitiveWeight (a / d))
      = primitiveWeightSum (primitiveDivisorQuotient A d) := by
  symm
  exact primitiveWeightSum_primitiveDivisorQuotient_eq A d

/--
Weighted fixed-divisor contribution expressed through the primitive quotient.
-/
theorem realVonMangoldt_mul_primitiveWeightSum_primitiveDivisorQuotient_eq
    (A : Finset ℕ) (d : ℕ) :
    realVonMangoldt d * primitiveWeightSum (primitiveDivisorQuotient A d)
      =
    Finset.sum (primitiveDivisorFiber A d)
      (fun a => realVonMangoldt d * primitiveWeight (a / d)) := by
  rw [primitiveWeightSum_primitiveDivisorQuotient_eq]
  rw [Finset.mul_sum]

/--
Repackage the divisor sigma-sum against the quotient primitive weight as an
outer finite sum over divisors, with inner fibers collapsed to quotient
primitive-weight sums.

The explicit nonzero-support hypothesis excludes the degenerate `a = 0` case,
for which `a.divisors = ∅` but `d ∣ a` would otherwise create spurious fiber
terms on the quotient side.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_quotient_eq
    (A : Finset ℕ) (hA0 : ∀ ⦃a : ℕ⦄, a ∈ A → a ≠ 0) :
    Finset.sum (A.sigma fun a => a.divisors)
      (fun x => realVonMangoldt x.2 * primitiveWeight (x.1 / x.2))
      =
    Finset.sum (A.biUnion fun a => a.divisors)
      (fun d => realVonMangoldt d * primitiveWeightSum (primitiveDivisorQuotient A d)) := by
  let s := A.sigma fun a => a.divisors
  let t := (A.biUnion fun a => a.divisors).sigma fun d => primitiveDivisorFiber A d
  have hswap :
      Finset.sum s (fun x => realVonMangoldt x.2 * primitiveWeight (x.1 / x.2))
        =
      Finset.sum t (fun y => realVonMangoldt y.1 * primitiveWeight (y.2 / y.1)) := by
    refine Finset.sum_bij'
      (fun x hx => ⟨x.2, x.1⟩)
      (fun y hy => ⟨y.2, y.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx' : x ∈ A.sigma (fun a => a.divisors) := by
        simpa only [s] using hx
      rcases Finset.mem_sigma.mp hx' with ⟨hxA, hxd⟩
      refine Finset.mem_sigma.mpr ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨x.1, hxA, hxd⟩
      · exact Finset.mem_filter.mpr ⟨hxA, (Nat.mem_divisors.mp hxd).1⟩
    · intro y hy
      have hy' : y ∈ (A.biUnion fun a => a.divisors).sigma (fun d => primitiveDivisorFiber A d) := by
        simpa only [t] using hy
      rcases Finset.mem_sigma.mp hy' with ⟨hyD, hyF⟩
      have hyA : y.2 ∈ A := primitiveDivisorFiber_mem hyF
      have hyDiv : y.1 ∣ y.2 := primitiveDivisorFiber_dvd hyF
      refine Finset.mem_sigma.mpr ?_
      refine ⟨hyA, Nat.mem_divisors.mpr ⟨hyDiv, ?_⟩⟩
      exact hA0 hyA
    · intro x hx
      rfl
    · intro y hy
      rfl
    · intro x hx
      rfl
  calc
    Finset.sum (A.sigma fun a => a.divisors)
        (fun x => realVonMangoldt x.2 * primitiveWeight (x.1 / x.2))
      = Finset.sum s (fun x => realVonMangoldt x.2 * primitiveWeight (x.1 / x.2)) := by
          rfl
    _ = Finset.sum t (fun y => realVonMangoldt y.1 * primitiveWeight (y.2 / y.1)) := hswap
    _ = Finset.sum (A.biUnion fun a => a.divisors)
          (fun d => Finset.sum (primitiveDivisorFiber A d)
            (fun a => realVonMangoldt d * primitiveWeight (a / d))) := by
          simpa only [t] using
            (Finset.sum_sigma'
              (s := A.biUnion fun a => a.divisors)
              (t := fun d => primitiveDivisorFiber A d)
              (f := fun d a => realVonMangoldt d * primitiveWeight (a / d))).symm
    _ = Finset.sum (A.biUnion fun a => a.divisors)
          (fun d => realVonMangoldt d * primitiveWeightSum (primitiveDivisorQuotient A d)) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          symm
          exact realVonMangoldt_mul_primitiveWeightSum_primitiveDivisorQuotient_eq A d

theorem supportedAboveFinset_one_nonzero {A : Finset ℕ}
    (hA : SupportedAboveFinset 1 A) :
    ∀ ⦃a : ℕ⦄, a ∈ A → a ≠ 0 := by
  intro a ha
  have h1 : 1 ≤ a := hA ha
  exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one h1)

/--
Supported-above-`1` specialization of the divisor-swapped quotient identity.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_quotient_eq_of_supportedAbove
    (A : Finset ℕ) (hA : SupportedAboveFinset 1 A) :
    Finset.sum (A.sigma fun a => a.divisors)
      (fun x => realVonMangoldt x.2 * primitiveWeight (x.1 / x.2))
      =
    Finset.sum (A.biUnion fun a => a.divisors)
      (fun d => realVonMangoldt d * primitiveWeightSum (primitiveDivisorQuotient A d)) := by
  exact primitiveWeight_vonMangoldt_divisorSigma_quotient_eq A
    (supportedAboveFinset_one_nonzero hA)

theorem supportedAboveFinset_mono {x y : ℕ} {A : Finset ℕ}
    (hxy : y ≤ x) (hA : SupportedAboveFinset x A) :
    SupportedAboveFinset y A := by
  intro n hn
  exact le_trans hxy (hA hn)

theorem supportedAbove_mono {x y : ℕ} {A : Set ℕ}
    (hxy : y ≤ x) (hA : SupportedAbove x A) :
    SupportedAbove y A := by
  intro n hn
  exact le_trans hxy (hA hn)

end InfoGeometry.Arithmetic
