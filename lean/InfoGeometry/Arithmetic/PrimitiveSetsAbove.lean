import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import InfoGeometry.Meta.BridgeTarget

/-!
InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean

Lean owner surface for the primitive-set problem with weight `1 / (n log n)`.

This module does not claim the analytic proof. It formalizes:

* the primitive-set predicate;
* the weighted finite and infinite sums;
* support-above-`x` conditions;
* faithful theorem statements for the finite and infinite forms;
* Mellin/modular integral representations of the primitive weight;
* finite divisor-fiber reindexing lemmas for von Mangoldt weights.
-/

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

/-- Finite set of primes in a closed interval. -/
def primeFinsetIcc (x N : ℕ) : Finset ℕ :=
  (Finset.Icc x N).filter Nat.Prime

/-- The finite prime interval is primitive. -/
theorem primeFinsetIcc_primitive
    (x N : ℕ) :
    PrimitiveFinset (primeFinsetIcc x N) := by
  intro a b ha hb hab
  classical
  have ha' : a ∈ primeFinsetIcc x N := by simpa using ha
  have hb' : b ∈ primeFinsetIcc x N := by simpa using hb
  have haPrime : Nat.Prime a := (Finset.mem_filter.mp ha').2
  have hbPrime : Nat.Prime b := (Finset.mem_filter.mp hb').2
  exact ((hbPrime.dvd_iff_eq haPrime.ne_one).mp hab).symm

/-- The finite prime interval is supported above its lower endpoint. -/
theorem primeFinsetIcc_supportedAbove
  (x N : ℕ) :
    SupportedAboveFinset x (primeFinsetIcc x N) := by
  intro n hn
  have hn' : n ∈ primeFinsetIcc x N := by simpa using hn
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn').1).1

/-- Finite primitive-set weighted sum. -/
def primitiveWeightSum (A : Finset ℕ) : ℝ :=
  Finset.sum A primitiveWeight

/--
Primitive-weight sum after scaling the support by a fixed divisor `d`.

This is the quotient-side readout that naturally appears after rewriting a
divisor fiber `a = d * m`.
-/
def primitiveScaledWeightSum (A : Finset ℕ) (d : ℕ) : ℝ :=
  Finset.sum A (fun m => primitiveWeight (d * m))

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

/-! ## Primitive/support monotonicity -/

/-- Primitive-set property is inherited by subsets. -/
theorem PrimitiveSet.mono
    {A B : Set ℕ}
    (hA : PrimitiveSet A)
    (hBA : B ⊆ A) :
    PrimitiveSet B := by
  intro a b ha hb hab
  exact hA (hBA ha) (hBA hb) hab

/-- Primitive-finset property is inherited by sub-finsets. -/
theorem PrimitiveFinset.mono
    {A B : Finset ℕ}
    (hA : PrimitiveFinset A)
    (hBA : B ⊆ A) :
    PrimitiveFinset B := by
  intro a b ha hb hab
  exact hA (hBA ha) (hBA hb) hab

/-- Support-above is inherited by subsets. -/
theorem SupportedAbove.subset
    {x : ℕ} {A B : Set ℕ}
    (hA : SupportedAbove x A)
    (hBA : B ⊆ A) :
    SupportedAbove x B := by
  intro n hn
  exact hA (hBA hn)

/-- Finite support-above is inherited by sub-finsets. -/
theorem SupportedAboveFinset.subset
    {x : ℕ} {A B : Finset ℕ}
    (hA : SupportedAboveFinset x A)
    (hBA : B ⊆ A) :
    SupportedAboveFinset x B := by
  intro n hn
  exact hA (hBA hn)

/-- Coercion form for finite primitive sets. -/
theorem PrimitiveFinset_iff
    (A : Finset ℕ) :
    PrimitiveFinset A ↔ PrimitiveSet (A : Set ℕ) := by
  rfl

/-- Coercion form for finite support-above. -/
theorem SupportedAboveFinset_iff
    (x : ℕ)
    (A : Finset ℕ) :
    SupportedAboveFinset x A ↔ SupportedAbove x (A : Set ℕ) := by
  rfl

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

/-! ## Positive-weight support facts -/

/--
If a set is supported above `2`, every member lies in the positive-weight
range.
-/
theorem one_lt_of_mem_supportedAbove_two
    {A : Set ℕ}
    (hA : SupportedAbove 2 A)
    {n : ℕ}
    (hn : n ∈ A) :
    1 < n :=
  lt_of_lt_of_le Nat.one_lt_two (hA hn)

/--
If a finset is supported above `2`, every member lies in the positive-weight
range.
-/
theorem one_lt_of_mem_supportedAboveFinset_two
    {A : Finset ℕ}
    (hA : SupportedAboveFinset 2 A)
    {n : ℕ}
    (hn : n ∈ A) :
    1 < n :=
  one_lt_of_mem_supportedAbove_two hA hn

/--
If a finset is supported above `2`, every member has positive primitive weight.
-/
theorem primitiveWeight_pos_of_mem_supportedAboveFinset_two
    {A : Finset ℕ}
    (hA : SupportedAboveFinset 2 A)
    {n : ℕ}
    (hn : n ∈ A) :
    0 < primitiveWeight n :=
  primitiveWeight_pos (one_lt_of_mem_supportedAboveFinset_two hA hn)

/-- A primitive set restricted to the positive-weight range. -/
def PrimitiveSetAboveTwo
    (A : Set ℕ) : Prop :=
  PrimitiveSet A ∧ SupportedAbove 2 A

/-- A finite primitive set restricted to the positive-weight range. -/
def PrimitiveFinsetAboveTwo
    (A : Finset ℕ) : Prop :=
  PrimitiveFinset A ∧ SupportedAboveFinset 2 A

/-! ## Big-O denominator facts -/

/-- If `2 ≤ x`, then `log x > 0`. -/
theorem log_nat_pos_of_two_le
    {x : ℕ}
    (hx : 2 ≤ x) :
    0 < Real.log (x : ℝ) :=
  Real.log_pos (by exact_mod_cast hx)

/-- If `2 ≤ x`, then `1 / log x ≥ 0`. -/
theorem one_div_log_nat_nonneg_of_two_le
    {x : ℕ}
    (hx : 2 ≤ x) :
    0 ≤ 1 / Real.log (x : ℝ) :=
  (one_div_pos.mpr (log_nat_pos_of_two_le hx)).le

/-- If `C ≥ 0` and `2 ≤ x`, then `C / log x ≥ 0`. -/
theorem div_log_nat_nonneg_of_two_le
    {C : ℝ} {x : ℕ}
    (hC : 0 ≤ C)
    (hx : 2 ≤ x) :
    0 ≤ C / Real.log (x : ℝ) :=
  div_nonneg hC (log_nat_pos_of_two_le hx).le

/--
Primitive-weight sums are monotone under finite support inclusion.
-/
theorem primitiveWeightSum_mono
    {A B : Finset ℕ}
    (hAB : A ⊆ B) :
    primitiveWeightSum A ≤ primitiveWeightSum B := by
  unfold primitiveWeightSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    hAB
    (by
      intro x _hxB _hxA
      exact primitiveWeight_nonneg x)

/-! ## Indicator-series facts -/

theorem primitiveIndicatorSeries_apply_mem
    (A : Set ℕ) {n : ℕ}
    (hn : n ∈ A) :
    primitiveIndicatorSeries A n = primitiveWeight n := by
  classical
  simp [primitiveIndicatorSeries, hn]

theorem primitiveIndicatorSeries_apply_not_mem
    (A : Set ℕ) {n : ℕ}
    (hn : n ∉ A) :
    primitiveIndicatorSeries A n = 0 := by
  classical
  simp [primitiveIndicatorSeries, hn]

theorem primitiveIndicatorSeries_nonneg
    (A : Set ℕ)
    (n : ℕ) :
    0 ≤ primitiveIndicatorSeries A n := by
  classical
  by_cases hn : n ∈ A
  · rw [primitiveIndicatorSeries_apply_mem A hn]
    exact primitiveWeight_nonneg n
  · rw [primitiveIndicatorSeries_apply_not_mem A hn]

theorem primitiveWeight_mul_eq_of_right_one (d : ℕ) :
    primitiveWeight (d * 1) = primitiveWeight d := by
  simp

/--
Scaling the argument by a factor `d ≥ 1` can only decrease the primitive
weight, once the right factor is already strictly above `1`.
-/
theorem primitiveWeight_mul_le_of_one_lt_right
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 < m) :
    primitiveWeight (d * m) ≤ primitiveWeight m := by
  have hmul_ge : m ≤ d * m := by
    simpa [Nat.one_mul, Nat.mul_comm] using Nat.mul_le_mul_right m hd
  have hdm : 1 < d * m := lt_of_lt_of_le hm hmul_ge
  rw [primitiveWeight, if_pos hdm, primitiveWeight, if_pos hm]
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hm)
  have hcast_le : (m : ℝ) ≤ (d * m : ℕ) := by
    exact_mod_cast hmul_ge
  have hlog_le : Real.log m ≤ Real.log (d * m) := by
    have hcast_mul : (m : ℝ) ≤ (d : ℝ) * (m : ℝ) := by
      exact_mod_cast hmul_ge
    simpa [Nat.cast_mul] using Real.log_le_log hm_pos hcast_mul
  have hlog_nonneg : 0 ≤ Real.log (d * m) := by
    exact Real.log_nonneg (show (1 : ℝ) ≤ d * m by
      exact_mod_cast (Nat.le_of_lt hdm))
  have hden_left :
      (m : ℝ) * Real.log m ≤ (m : ℝ) * Real.log (d * m) := by
    exact mul_le_mul_of_nonneg_left hlog_le hm_pos.le
  have hden_right :
      (m : ℝ) * Real.log (d * m) ≤ ((d * m : ℕ) : ℝ) * Real.log (d * m) := by
    exact mul_le_mul_of_nonneg_right hcast_le hlog_nonneg
  have hden :
      (m : ℝ) * Real.log m ≤ ((d * m : ℕ) : ℝ) * Real.log (d * m) := by
    exact le_trans hden_left hden_right
  have hden' :
      (m : ℝ) * Real.log m ≤ ((d * m : ℕ) : ℝ) * Real.log ((d * m : ℕ) : ℝ) := by
    simpa [Nat.cast_mul] using hden
  exact one_div_le_one_div_of_le (mul_pos hm_pos (Real.log_pos (by exact_mod_cast hm))) hden'

/--
Away from the special quotient atom `m = 1`, scaling by `d ≥ 1` does not
increase the primitive weight.
-/
theorem primitiveWeight_mul_le_of_ne_one
    {d m : ℕ} (hd : 1 ≤ d) (hm1 : m ≠ 1) :
    primitiveWeight (d * m) ≤ primitiveWeight m := by
  by_cases hm : 1 < m
  · exact primitiveWeight_mul_le_of_one_lt_right hd hm
  · have hm_le : m ≤ 1 := le_of_not_gt hm
    have hm_zero : m = 0 := by
      omega
    simp [hm_zero, primitiveWeight_eq_zero_of_le_one]

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

/-! ## Projective finite count profiles -/

/-- A finite count profile has nonzero total mass on support `A`. -/
def HasNonzeroArithmeticMass
    (A : Finset ℕ)
    (counts : ℕ → ℝ) : Prop :=
  arithmeticTotalMass A counts ≠ 0

/-- A finite count profile has positive total mass on support `A`. -/
def HasPositiveArithmeticMass
    (A : Finset ℕ)
    (counts : ℕ → ℝ) : Prop :=
  0 < arithmeticTotalMass A counts

/--
The normalized base shape has total mass one when the original total mass is
nonzero.
-/
theorem arithmeticBaseShape_totalMass_eq_one
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (hmass : arithmeticTotalMass A counts ≠ 0) :
    Finset.sum A (arithmeticBaseShape A counts) = 1 := by
  unfold arithmeticBaseShape arithmeticTotalMass
  calc
    Finset.sum A (fun n => counts n / Finset.sum A counts)
        = (Finset.sum A counts) / (Finset.sum A counts) := by
          rw [Finset.sum_div]
    _ = 1 := by
          exact div_self hmass

/--
The normalized base shape is nonnegative on the support when counts are
nonnegative and total mass is positive.
-/
theorem arithmeticBaseShape_nonneg
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (hmass : 0 < arithmeticTotalMass A counts)
    (hcounts : ∀ ⦃n : ℕ⦄, n ∈ A → 0 ≤ counts n)
    {n : ℕ}
    (hn : n ∈ A) :
    0 ≤ arithmeticBaseShape A counts n := by
  unfold arithmeticBaseShape
  exact div_nonneg (hcounts hn) hmass.le

/-! ## Arithmetic modular rays -/

/--
An arithmetic partition has nonzero Mellin/modular mass on support `A`.

This is the scale component of the finite arithmetic exponential family.
-/
def HasNonzeroArithmeticPartition
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ) : Prop :=
  arithmeticPartition A counts s ≠ 0

/--
An arithmetic partition has positive Mellin/modular mass on support `A`.
-/
def HasPositiveArithmeticPartition
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ) : Prop :=
  0 < arithmeticPartition A counts s

/--
Normalized arithmetic Boltzmann ray.

The unnormalized weight is `counts n * n^{-s}`.  The ray divides by the finite
partition `Z_c(s) = ∑ n ∈ A, counts n n^{-s}`.
-/
def arithmeticBoltzmannRay
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ)
    (n : ℕ) : ℝ :=
  arithmeticCountWeight counts s n / arithmeticPartition A counts s

/--
The arithmetic Boltzmann ray has total mass one when the partition is nonzero.
-/
theorem arithmeticBoltzmannRay_totalMass_eq_one
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ)
    (hZ : arithmeticPartition A counts s ≠ 0) :
    Finset.sum A (arithmeticBoltzmannRay A counts s) = 1 := by
  unfold arithmeticBoltzmannRay arithmeticPartition
  calc
    Finset.sum A
        (fun n => arithmeticCountWeight counts s n /
          Finset.sum A (arithmeticCountWeight counts s))
        = Finset.sum A (arithmeticCountWeight counts s) /
          Finset.sum A (arithmeticCountWeight counts s) := by
            rw [Finset.sum_div]
    _ = 1 := by
          exact div_self hZ

/--
The arithmetic Boltzmann ray is nonnegative on support when counts are
nonnegative and the partition is positive.
-/
theorem arithmeticBoltzmannRay_nonneg
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ)
    (hZ : 0 < arithmeticPartition A counts s)
    (hcounts : ∀ ⦃n : ℕ⦄, n ∈ A → 0 ≤ counts n)
    {n : ℕ}
    (hn : n ∈ A) :
    0 ≤ arithmeticBoltzmannRay A counts s n := by
  unfold arithmeticBoltzmannRay arithmeticCountWeight
  exact div_nonneg
    (mul_nonneg (hcounts hn) (primitiveMellinKernel_nonneg n s))
    hZ.le

/--
Scale-shape reconstruction of the unnormalized arithmetic weight from the
partition scale and normalized ray.
-/
theorem arithmeticCountWeight_eq_partition_mul_boltzmannRay
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ)
    (n : ℕ)
    (hZ : arithmeticPartition A counts s ≠ 0) :
    arithmeticCountWeight counts s n =
      arithmeticPartition A counts s * arithmeticBoltzmannRay A counts s n := by
  unfold arithmeticBoltzmannRay
  field_simp [hZ]

/--
Equivalent reconstruction with the scale on the right.
-/
theorem arithmeticCountWeight_eq_boltzmannRay_mul_partition
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ)
    (n : ℕ)
    (hZ : arithmeticPartition A counts s ≠ 0) :
    arithmeticCountWeight counts s n =
      arithmeticBoltzmannRay A counts s n * arithmeticPartition A counts s := by
  rw [mul_comm]
  exact arithmeticCountWeight_eq_partition_mul_boltzmannRay A counts s n hZ

/--
Finite arithmetic exponential-family packet.

This records the unnormalized modular weight, its partition scale, and the
normalized projective ray.  It is the commutative arithmetic shadow of the
operatorial exponential-family lane.
-/
structure ArithmeticExponentialRay
    (A : Finset ℕ)
    (counts : ℕ → ℝ)
    (s : ℝ) where
  /-- Positivity of the partition scale. -/
  partition_pos :
    0 < arithmeticPartition A counts s

namespace ArithmeticExponentialRay

variable {A : Finset ℕ} {counts : ℕ → ℝ} {s : ℝ}
variable (R : ArithmeticExponentialRay A counts s)

/-- The scale of the arithmetic exponential ray. -/
def scale
    (_R : ArithmeticExponentialRay A counts s) : ℝ :=
  arithmeticPartition A counts s

/-- The normalized shape/ray of the arithmetic exponential family. -/
def shape
    (_R : ArithmeticExponentialRay A counts s)
    (n : ℕ) : ℝ :=
  arithmeticBoltzmannRay A counts s n

/-- The scale is positive. -/
theorem scale_pos :
    0 < scale R :=
  R.partition_pos

/-- The normalized shape has total mass one. -/
theorem shape_totalMass_eq_one :
    Finset.sum A (shape R) = 1 :=
  arithmeticBoltzmannRay_totalMass_eq_one A counts s R.partition_pos.ne'

/-- The unnormalized arithmetic weight is scale times shape. -/
theorem weight_eq_scale_mul_shape
    (n : ℕ) :
    arithmeticCountWeight counts s n = scale R * shape R n :=
  arithmeticCountWeight_eq_partition_mul_boltzmannRay A counts s n R.partition_pos.ne'

end ArithmeticExponentialRay

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
  intro a b ha hb hab
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

theorem primitiveFinset_erase {A : Finset ℕ} (hA : PrimitiveFinset A) (n : ℕ) :
    PrimitiveFinset (A.erase n) := by
  intro a b ha hb hab
  exact hA (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab

theorem supportedAboveFinset_erase {x : ℕ} {A : Finset ℕ} (hA : SupportedAboveFinset x A)
    (n : ℕ) : SupportedAboveFinset x (A.erase n) := by
  intro m hm
  exact hA (Finset.mem_of_mem_erase hm)

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
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ}
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
  exact congrArg (fun t : ℕ => t / d) hab_eq

/--
Backward-compatible wrapper with the old explicit nonzero divisor argument.
The nonzero argument is not needed for the proof.
-/
theorem primitiveFinset_image_div_of_nonzero
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ} (_hd0 : d ≠ 0)
    (hdiv : ∀ ⦃a : ℕ⦄, a ∈ A → d ∣ a) :
    PrimitiveFinset (A.image fun a => a / d) :=
  primitiveFinset_image_div hA hdiv

theorem primitiveDivisorQuotient_primitive
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ} :
    PrimitiveFinset (primitiveDivisorQuotient A d) := by
  apply primitiveFinset_image_div
  · intro a b ha hb hab
    exact hA (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

/--
Backward-compatible wrapper with the old explicit nonzero divisor argument.
The nonzero argument is not needed for the quotient primitive proof.
-/
theorem primitiveDivisorQuotient_primitive_of_nonzero
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ} (_hd0 : d ≠ 0) :
    PrimitiveFinset (primitiveDivisorQuotient A d) :=
  primitiveDivisorQuotient_primitive hA

theorem primitiveDivisorQuotient_supportedAbove
    {A : Finset ℕ} {x d : ℕ} (hA : SupportedAboveFinset x A) :
    SupportedAboveFinset (x / d) (primitiveDivisorQuotient A d) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
  have haA : a ∈ A := (Finset.mem_filter.mp ha).1
  exact Nat.div_le_div_right (hA haA)

theorem primitiveDivisorQuotient_erase_one_primitive
    {A : Finset ℕ} (hA : PrimitiveFinset A) {d : ℕ} (_hd0 : d ≠ 0) :
    PrimitiveFinset ((primitiveDivisorQuotient A d).erase 1) := by
  exact primitiveFinset_erase (primitiveDivisorQuotient_primitive hA) 1

theorem primitiveDivisorQuotient_erase_one_supportedAbove
    {A : Finset ℕ} {x d : ℕ} (hA : SupportedAboveFinset x A) :
    SupportedAboveFinset (x / d) ((primitiveDivisorQuotient A d).erase 1) := by
  exact supportedAboveFinset_erase (primitiveDivisorQuotient_supportedAbove hA) 1

theorem primitiveDivisorQuotient_erase_one_supportedAbove_two
    {A : Finset ℕ} {d : ℕ} (hA : SupportedAboveFinset 1 A) :
    SupportedAboveFinset 2 ((primitiveDivisorQuotient A d).erase 1) := by
  intro n hn
  rcases Finset.mem_erase.mp hn with ⟨hn1, hnQ⟩
  rcases Finset.mem_image.mp hnQ with ⟨a, ha, hEq⟩
  have haA : a ∈ A := (Finset.mem_filter.mp ha).1
  have hda : d ∣ a := (Finset.mem_filter.mp ha).2
  have ha_pos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one (hA haA)
  have hrepr : a = d * (a / d) := by rw [Nat.mul_div_cancel' hda]
  have hq_ne_zero : a / d ≠ 0 := by
    intro hq0
    rw [hq0, Nat.mul_zero] at hrepr
    exact (Nat.ne_of_gt ha_pos) hrepr
  have hq_pos : 0 < a / d := Nat.pos_of_ne_zero hq_ne_zero
  have hq_ge_one : 1 ≤ a / d := Nat.succ_le_of_lt hq_pos
  have hq_ne_one : a / d ≠ 1 := by
    intro hq1
    exact hn1 (hEq.symm.trans hq1)
  have hq_gt_one : 1 < a / d := lt_of_le_of_ne hq_ge_one hq_ne_one.symm
  simpa [hEq] using Nat.succ_le_of_lt hq_gt_one

theorem primitiveDivisorQuotient_erase_one_supportedAbove_max
    {A : Finset ℕ} {x d : ℕ} (hx : 1 ≤ x) (hA : SupportedAboveFinset x A) :
    SupportedAboveFinset (max (x / d) 2) ((primitiveDivisorQuotient A d).erase 1) := by
  intro n hn
  have hxdiv : x / d ≤ n := primitiveDivisorQuotient_erase_one_supportedAbove hA hn
  have hA1 : SupportedAboveFinset 1 A := by
    intro a ha
    exact le_trans hx (hA ha)
  have htwo : 2 ≤ n := primitiveDivisorQuotient_erase_one_supportedAbove_two hA1 hn
  exact max_le_iff.mpr ⟨hxdiv, htwo⟩

/--
Bootstrap the residual quotient support back into the finite primitive-sets-
above statement, once the transported threshold `max (x / d) 2` lies inside
the statement's validity range.
-/
theorem primitiveWeightSum_primitiveDivisorQuotient_erase_one_le_of_finiteStatement
    (hfin : PrimitiveSetsAboveFiniteStatement) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ {A : Finset ℕ} {x d : ℕ},
      x₀ ≤ max (x / d) 2 →
      PrimitiveFinset A →
      SupportedAboveFinset x A →
      1 ≤ x →
      1 ≤ d →
      primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1) ≤ 1 + ε := by
  rcases hfin ε hε with ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  intro A x d hthresh hAprim hAsupp hx hd
  apply hx₀ hthresh
  · exact primitiveDivisorQuotient_erase_one_primitive hAprim (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  · exact primitiveDivisorQuotient_erase_one_supportedAbove_max hx hAsupp

theorem primitiveDivisorQuotient_one_mem_iff {A : Finset ℕ} {d : ℕ} (hd0 : d ≠ 0) :
    1 ∈ primitiveDivisorQuotient A d ↔ d ∈ A := by
  constructor
  · intro h1
    rcases Finset.mem_image.mp h1 with ⟨a, ha, ha1⟩
    have haA : a ∈ A := (Finset.mem_filter.mp ha).1
    have hda : d ∣ a := (Finset.mem_filter.mp ha).2
    have hEq : a = d := by
      have ha1' : a / d = 1 := by simpa using ha1
      calc
        a = d * (a / d) := by rw [Nat.mul_div_cancel' hda]
        _ = d * 1 := by rw [ha1']
        _ = d := by simp
    simpa [hEq] using haA
  · intro hdA
    refine Finset.mem_image.mpr ?_
    refine ⟨d, Finset.mem_filter.mpr ⟨hdA, dvd_rfl⟩, ?_⟩
    exact Nat.div_self (Nat.pos_of_ne_zero hd0)

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

/--
Division by a fixed `d` is injective on the `d`-divisible fiber.

No `d ≠ 0` hypothesis is needed: when `d = 0`, the fiber consists only of
elements divisible by `0`, hence only `0`.
-/
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
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    have hda : d ∣ a := primitiveDivisorFiber_dvd ha
    rw [Nat.mul_div_cancel' hda]
  · intro a ha b hb hab
    exact primitiveDivisorFiber_div_injective ha hb hab

/--
Specialization of the fixed-divisor reindexing to the primitive weight.
-/
theorem primitiveWeightSum_primitiveDivisorQuotient_eq
    (A : Finset ℕ) (d : ℕ) :
    primitiveWeightSum (primitiveDivisorQuotient A d)
      = Finset.sum (primitiveDivisorFiber A d) (fun a => primitiveWeight (a / d)) := by
  unfold primitiveWeightSum
  rw [primitiveDivisorQuotient_eq_image_fiber]
  rw [Finset.sum_image]
  · intro a ha b hb hab
    exact primitiveDivisorFiber_div_injective ha hb hab

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
Fixed-divisor fiber of the original primitive weight, expressed as a scaled
primitive-weight sum on the quotient support.
-/
theorem sum_primitiveDivisorFiber_primitiveWeight_eq_primitiveScaledWeightSum
    (A : Finset ℕ) (d : ℕ) :
    Finset.sum (primitiveDivisorFiber A d) primitiveWeight
      =
    primitiveScaledWeightSum (primitiveDivisorQuotient A d) d := by
  unfold primitiveScaledWeightSum
  exact sum_primitiveDivisorFiber_eq_sum_primitiveDivisorQuotient A
    (d := d) primitiveWeight

/--
Weighted fixed-divisor contribution of the original primitive weight, written
through the quotient support with the scaling parameter retained.
-/
theorem realVonMangoldt_mul_primitiveScaledWeightSum_primitiveDivisorQuotient_eq
    (A : Finset ℕ) (d : ℕ) :
    realVonMangoldt d * primitiveScaledWeightSum (primitiveDivisorQuotient A d) d
      =
    Finset.sum (primitiveDivisorFiber A d)
      (fun a => realVonMangoldt d * primitiveWeight a) := by
  rw [← sum_primitiveDivisorFiber_primitiveWeight_eq_primitiveScaledWeightSum]
  rw [Finset.mul_sum]

/--
Scaled primitive-weight sums are controlled by the ordinary primitive-weight
sum after splitting off the exceptional quotient atom `1`.
-/
theorem primitiveScaledWeightSum_le_if_mem_add_erase
    (A : Finset ℕ) {d : ℕ} (hd : 1 ≤ d) :
    primitiveScaledWeightSum A d
      ≤ (if 1 ∈ A then primitiveWeight d else 0) + primitiveWeightSum (A.erase 1) := by
  classical
  by_cases h1 : 1 ∈ A
  · calc
      primitiveScaledWeightSum A d
          = Finset.sum (A.erase 1) (fun m => primitiveWeight (d * m)) + primitiveWeight (d * 1) := by
              unfold primitiveScaledWeightSum
              simpa using (Finset.sum_erase_add (s := A) (f := fun m => primitiveWeight (d * m)) h1).symm
      _ ≤ Finset.sum (A.erase 1) primitiveWeight + primitiveWeight d := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro m hm
              exact primitiveWeight_mul_le_of_ne_one hd (Finset.mem_erase.mp hm).1
            · simp
      _ = (if 1 ∈ A then primitiveWeight d else 0) + primitiveWeightSum (A.erase 1) := by
            simp [primitiveWeightSum, h1, add_comm]
  · calc
      primitiveScaledWeightSum A d = Finset.sum (A.erase 1) (fun m => primitiveWeight (d * m)) := by
        simp [primitiveScaledWeightSum, h1]
      _ ≤ primitiveWeightSum (A.erase 1) := by
        unfold primitiveWeightSum
        apply Finset.sum_le_sum
        intro m hm
        exact primitiveWeight_mul_le_of_ne_one hd (Finset.mem_erase.mp hm).1
      _ = (if 1 ∈ A then primitiveWeight d else 0) + primitiveWeightSum (A.erase 1) := by
        simp [h1]

/--
Specialize the scaled primitive-weight bound to a quotient support and rewrite
the exceptional `1`-atom as membership of the original divisor `d`.
-/
theorem primitiveScaledWeightSum_primitiveDivisorQuotient_le
    (A : Finset ℕ) {d : ℕ} (hd : 1 ≤ d) :
    primitiveScaledWeightSum (primitiveDivisorQuotient A d) d
      ≤ (if d ∈ A then primitiveWeight d else 0)
          + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1) := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd)
  simpa [primitiveDivisorQuotient_one_mem_iff hd0] using
    (primitiveScaledWeightSum_le_if_mem_add_erase (A := primitiveDivisorQuotient A d) hd)

/--
The same quotient-side bound after multiplying by the nonnegative von Mangoldt
weight at the outer divisor `d`.
-/
theorem realVonMangoldt_mul_primitiveScaledWeightSum_primitiveDivisorQuotient_le
    (A : Finset ℕ) {d : ℕ} (hd : 1 ≤ d) :
    realVonMangoldt d * primitiveScaledWeightSum (primitiveDivisorQuotient A d) d
      ≤ realVonMangoldt d
          * ((if d ∈ A then primitiveWeight d else 0)
              + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1)) := by
  exact mul_le_mul_of_nonneg_left
    (primitiveScaledWeightSum_primitiveDivisorQuotient_le A hd)
    (realVonMangoldt_nonneg d)

/--
Repackage the original divisor sigma-sum as an outer finite sum over divisors,
with each inner divisor fiber rewritten as a scaled primitive-weight sum on the
quotient support.

The explicit nonzero-support hypothesis excludes the degenerate `a = 0` case,
for which `a.divisors = ∅` but `d ∣ a` would otherwise create spurious fiber
terms on the quotient side.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_eq
    (A : Finset ℕ) (hA0 : ∀ ⦃a : ℕ⦄, a ∈ A → a ≠ 0) :
    Finset.sum (A.sigma fun a => a.divisors)
      (fun x => primitiveWeight x.1 * realVonMangoldt x.2)
      =
    Finset.sum (A.biUnion fun a => a.divisors)
      (fun d => realVonMangoldt d * primitiveScaledWeightSum (primitiveDivisorQuotient A d) d) := by
  let s := A.sigma fun a => a.divisors
  let t := (A.biUnion fun a => a.divisors).sigma fun d => primitiveDivisorFiber A d
  have hswap :
      Finset.sum s (fun x => primitiveWeight x.1 * realVonMangoldt x.2)
        =
      Finset.sum t (fun y => realVonMangoldt y.1 * primitiveWeight y.2) := by
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
      rw [mul_comm]
  calc
    Finset.sum (A.sigma fun a => a.divisors)
        (fun x => primitiveWeight x.1 * realVonMangoldt x.2)
      = Finset.sum s (fun x => primitiveWeight x.1 * realVonMangoldt x.2) := by
          rfl
    _ = Finset.sum t (fun y => realVonMangoldt y.1 * primitiveWeight y.2) := hswap
    _ = Finset.sum (A.biUnion fun a => a.divisors)
          (fun d => Finset.sum (primitiveDivisorFiber A d)
            (fun a => realVonMangoldt d * primitiveWeight a)) := by
          simpa only [t] using
            (Finset.sum_sigma'
              (s := A.biUnion fun a => a.divisors)
              (t := fun d => primitiveDivisorFiber A d)
              (f := fun d a => realVonMangoldt d * primitiveWeight a)).symm
    _ = Finset.sum (A.biUnion fun a => a.divisors)
          (fun d => realVonMangoldt d * primitiveScaledWeightSum (primitiveDivisorQuotient A d) d) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          symm
          exact realVonMangoldt_mul_primitiveScaledWeightSum_primitiveDivisorQuotient_eq A d

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

/--
Supported-above-`1` specialization of the scaled divisor-swapped identity.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_eq_of_supportedAbove
    (A : Finset ℕ) (hA : SupportedAboveFinset 1 A) :
    Finset.sum (A.sigma fun a => a.divisors)
      (fun x => primitiveWeight x.1 * realVonMangoldt x.2)
      =
    Finset.sum (A.biUnion fun a => a.divisors)
      (fun d => realVonMangoldt d * primitiveScaledWeightSum (primitiveDivisorQuotient A d) d) := by
  exact primitiveWeight_vonMangoldt_divisorSigma_scaled_eq A
    (supportedAboveFinset_one_nonzero hA)

/--
Supported-above-`1` outer bound for the scaled divisor-swapped sigma-sum.

Each outer divisor contribution splits into a diagonal term indexed by `d ∈ A`
and a residual primitive-weight sum on the quotient support with the
exceptional quotient atom `1` removed.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_supportedAbove
    (A : Finset ℕ) (hA : SupportedAboveFinset 1 A) :
    Finset.sum (A.sigma fun a => a.divisors)
      (fun x => primitiveWeight x.1 * realVonMangoldt x.2)
      ≤
    Finset.sum (A.biUnion fun a => a.divisors)
      (fun d => realVonMangoldt d
        * ((if d ∈ A then primitiveWeight d else 0)
            + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1))) := by
  rw [primitiveWeight_vonMangoldt_divisorSigma_scaled_eq_of_supportedAbove A hA]
  apply Finset.sum_le_sum
  intro d hd
  rcases Finset.mem_biUnion.mp hd with ⟨a, haA, hddiv⟩
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_mem_divisors hddiv)
  exact realVonMangoldt_mul_primitiveScaledWeightSum_primitiveDivisorQuotient_le A hd1

/--
Bootstrap the supported-above scaled divisor bound through the finite
primitive-sets-above statement, provided every outer divisor `d` lands beyond
the threshold required for the residual quotient support.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_finiteStatement
    (hfin : PrimitiveSetsAboveFiniteStatement) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ {A : Finset ℕ} {x : ℕ},
      1 ≤ x →
      PrimitiveFinset A →
      SupportedAboveFinset x A →
      (∀ d ∈ A.biUnion (fun a => a.divisors), x₀ ≤ max (x / d) 2) →
      Finset.sum (A.sigma fun a => a.divisors)
        (fun y => primitiveWeight y.1 * realVonMangoldt y.2)
        ≤
      Finset.sum (A.biUnion fun a => a.divisors)
        (fun d => realVonMangoldt d * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε))) := by
  rcases primitiveWeightSum_primitiveDivisorQuotient_erase_one_le_of_finiteStatement hfin hε with
    ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  intro A x hx1 hAprim hAsupp hthresh
  have hA1 : SupportedAboveFinset 1 A := by
    intro a ha
    exact le_trans hx1 (hAsupp ha)
  refine le_trans (primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_supportedAbove A hA1) ?_
  apply Finset.sum_le_sum
  intro d hd
  rcases Finset.mem_biUnion.mp hd with ⟨a, haA, hddiv⟩
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_mem_divisors hddiv)
  have hq :
      primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1) ≤ 1 + ε := by
    apply hx₀
    · exact hthresh d hd
    · exact hAprim
    · exact hAsupp
    · exact hx1
    · exact hd1
  have hadd :
      (if d ∈ A then primitiveWeight d else 0)
          + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1)
        ≤
      (if d ∈ A then primitiveWeight d else 0) + (1 + ε) := by
    exact add_le_add_right hq _
  exact mul_le_mul_of_nonneg_left hadd (realVonMangoldt_nonneg d)

/--
Split the outer divisor sum into the regime where the finite-statement
bootstrap applies and the complementary finite exceptional regime.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_split_le_of_finiteStatement
    (hfin : PrimitiveSetsAboveFiniteStatement) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ {A : Finset ℕ} {x : ℕ},
      1 ≤ x →
      PrimitiveFinset A →
      SupportedAboveFinset x A →
      let D := A.biUnion (fun a => a.divisors)
      let good := D.filter (fun d => x₀ ≤ max (x / d) 2)
      let bad := D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)
      Finset.sum (A.sigma fun a => a.divisors)
          (fun y => primitiveWeight y.1 * realVonMangoldt y.2)
        ≤
      Finset.sum good
          (fun d => realVonMangoldt d * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε)))
        +
      Finset.sum bad
          (fun d => realVonMangoldt d
            * ((if d ∈ A then primitiveWeight d else 0)
                + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1))) := by
  rcases primitiveWeightSum_primitiveDivisorQuotient_erase_one_le_of_finiteStatement hfin hε with
    ⟨x₀, htail⟩
  refine ⟨x₀, ?_⟩
  intro A x hx hAprim hAsupp
  dsimp
  let D := A.biUnion (fun a => a.divisors)
  let F := fun d =>
    realVonMangoldt d * ((if d ∈ A then primitiveWeight d else 0)
      + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1))
  let G := fun d =>
    realVonMangoldt d * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε))
  have hbase :
      Finset.sum (A.sigma fun a => a.divisors)
          (fun y => primitiveWeight y.1 * realVonMangoldt y.2)
        ≤ Finset.sum D F := by
    apply primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_supportedAbove
    intro a ha
    exact le_trans hx (hAsupp ha)
  have hsplit :
      Finset.sum D F
        =
      Finset.sum (D.filter (fun d => x₀ ≤ max (x / d) 2)) F
        + Finset.sum (D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)) F := by
    simpa [D] using (Finset.sum_filter_add_sum_filter_not D (fun d => x₀ ≤ max (x / d) 2) F).symm
  have hgood :
      Finset.sum (D.filter (fun d => x₀ ≤ max (x / d) 2)) F
        ≤ Finset.sum (D.filter (fun d => x₀ ≤ max (x / d) 2)) G := by
    apply Finset.sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left
    · apply add_le_add_right
      apply htail
      · exact (Finset.mem_filter.mp hd).2
      · exact hAprim
      · exact hAsupp
      · exact hx
      · have hd1 : 1 ≤ d := by
          rcases Finset.mem_biUnion.mp ((Finset.mem_filter.mp hd).1) with ⟨a, haA, hddiv⟩
          exact Nat.succ_le_of_lt (Nat.pos_of_mem_divisors hddiv)
        exact hd1
    · exact realVonMangoldt_nonneg d
  calc
    Finset.sum (A.sigma fun a => a.divisors)
        (fun y => primitiveWeight y.1 * realVonMangoldt y.2)
      ≤ Finset.sum D F := hbase
    _ = Finset.sum (D.filter (fun d => x₀ ≤ max (x / d) 2)) F
          + Finset.sum (D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)) F := hsplit
    _ ≤ Finset.sum (D.filter (fun d => x₀ ≤ max (x / d) 2)) G
          + Finset.sum (D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)) F := by
          exact add_le_add hgood le_rfl

theorem badDivisorFilter_eq_empty_of_le_two {D : Finset ℕ} {x x₀ : ℕ} (hx₀ : x₀ ≤ 2) :
    D.filter (fun d => ¬ x₀ ≤ max (x / d) 2) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro d hd
  have hmax : x₀ ≤ max (x / d) 2 := le_trans hx₀ (le_max_right (x / d) 2)
  exact not_not_intro hmax

theorem mem_badDivisorFilter_imp_div_lt {D : Finset ℕ} {x x₀ d : ℕ}
    (hd : d ∈ D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)) :
    x / d < x₀ := by
  have hbad : ¬ x₀ ≤ max (x / d) 2 := (Finset.mem_filter.mp hd).2
  have hnot : ¬ x₀ ≤ x / d := by
    intro hxd
    exact hbad (le_trans hxd (le_max_left (x / d) 2))
  exact Nat.lt_of_not_ge hnot

theorem mem_badDivisorFilter_imp_two_lt {D : Finset ℕ} {x x₀ d : ℕ}
    (hd : d ∈ D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)) :
    2 < x₀ := by
  have hbad : ¬ x₀ ≤ max (x / d) 2 := (Finset.mem_filter.mp hd).2
  have hnot : ¬ x₀ ≤ 2 := by
    intro hx₂
    exact hbad (le_trans hx₂ (le_max_right (x / d) 2))
  exact Nat.lt_of_not_ge hnot

theorem mem_badDivisorFilter_imp_lt_mul {D : Finset ℕ} {x x₀ d : ℕ}
    (hd : d ∈ D.filter (fun d => ¬ x₀ ≤ max (x / d) 2)) (hdpos : 0 < d) :
    x < x₀ * d := by
  exact (Nat.div_lt_iff_lt_mul hdpos).mp (mem_badDivisorFilter_imp_div_lt hd)

theorem mem_badBiUnionDivisorFilter_imp_lt_mul {A : Finset ℕ} {x x₀ d : ℕ}
    (hd : d ∈ (A.biUnion fun a => a.divisors).filter (fun d => ¬ x₀ ≤ max (x / d) 2)) :
    x < x₀ * d := by
  have hdD : d ∈ A.biUnion fun a => a.divisors := (Finset.mem_filter.mp hd).1
  rcases Finset.mem_biUnion.mp hdD with ⟨a, haA, hdiv⟩
  exact mem_badDivisorFilter_imp_lt_mul hd (Nat.pos_of_mem_divisors hdiv)

theorem badBiUnionDivisorFilter_subset_largeDivisors (A : Finset ℕ) (x x₀ : ℕ) :
    (A.biUnion fun a => a.divisors).filter (fun d => ¬ x₀ ≤ max (x / d) 2)
      ⊆
    (A.biUnion fun a => a.divisors).filter (fun d => x < x₀ * d) := by
  intro d hd
  refine Finset.mem_filter.mpr ?_
  refine ⟨(Finset.mem_filter.mp hd).1, ?_⟩
  exact mem_badBiUnionDivisorFilter_imp_lt_mul hd

theorem badBiUnionDivisorFilter_sum_le_largeDivisor_sum (A : Finset ℕ) (x x₀ : ℕ) :
    Finset.sum ((A.biUnion fun a => a.divisors).filter (fun d => ¬ x₀ ≤ max (x / d) 2))
      (fun d => realVonMangoldt d
        * ((if d ∈ A then primitiveWeight d else 0)
            + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1)))
      ≤
    Finset.sum ((A.biUnion fun a => a.divisors).filter (fun d => x < x₀ * d))
      (fun d => realVonMangoldt d
        * ((if d ∈ A then primitiveWeight d else 0)
            + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1))) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact badBiUnionDivisorFilter_subset_largeDivisors A x x₀
  · intro d hd_large hd_not_bad
    have hterm_nonneg :
        0 ≤ realVonMangoldt d
          * ((if d ∈ A then primitiveWeight d else 0)
              + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1)) := by
      apply mul_nonneg
      · exact realVonMangoldt_nonneg d
      · apply add_nonneg
        · by_cases hdA : d ∈ A
          · simp [hdA, primitiveWeight_nonneg]
          · simp [hdA]
        · exact primitiveWeightSum_nonneg _
    exact hterm_nonneg

theorem mem_largeDivisorFilter_imp_div_lt {D : Finset ℕ} {x x₀ d : ℕ}
    (hd : d ∈ D.filter (fun d => x < x₀ * d)) (hx₀ : 0 < x₀) :
    x / x₀ < d := by
  have hmul : x < d * x₀ := by
    simpa [mul_comm] using (Finset.mem_filter.mp hd).2
  exact (Nat.div_lt_iff_lt_mul hx₀).mpr hmul

theorem largeBiUnionDivisorFilter_subset_divThreshold
    (A : Finset ℕ) (x x₀ : ℕ) (hx₀ : 0 < x₀) :
    (A.biUnion fun a => a.divisors).filter (fun d => x < x₀ * d)
      ⊆
    (A.biUnion fun a => a.divisors).filter (fun d => x / x₀ < d) := by
  intro d hd
  refine Finset.mem_filter.mpr ?_
  refine ⟨(Finset.mem_filter.mp hd).1, ?_⟩
  exact mem_largeDivisorFilter_imp_div_lt hd hx₀

/--
Final packaging of the current reduction lane: after bootstrapping the good
divisors through the finite statement, the only remaining contribution is the
explicit large-divisor slice `x < x₀ * d`.
-/
theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_largeDivisorSlice_of_finiteStatement
    (hfin : PrimitiveSetsAboveFiniteStatement) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ {A : Finset ℕ} {x : ℕ},
      1 ≤ x →
      PrimitiveFinset A →
      SupportedAboveFinset x A →
      let D := A.biUnion (fun a => a.divisors)
      let good := D.filter (fun d => x₀ ≤ max (x / d) 2)
      let large := D.filter (fun d => x < x₀ * d)
      Finset.sum (A.sigma fun a => a.divisors)
          (fun y => primitiveWeight y.1 * realVonMangoldt y.2)
        ≤
      Finset.sum good
          (fun d => realVonMangoldt d * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε)))
        +
      Finset.sum large
          (fun d => realVonMangoldt d
            * ((if d ∈ A then primitiveWeight d else 0)
                + primitiveWeightSum ((primitiveDivisorQuotient A d).erase 1))) := by
  rcases primitiveWeight_vonMangoldt_divisorSigma_scaled_split_le_of_finiteStatement hfin hε with
    ⟨x₀, hsplit⟩
  refine ⟨x₀, ?_⟩
  intro A x hx hAprim hAsupp
  dsimp
  refine le_trans (hsplit hx hAprim hAsupp) ?_
  apply add_le_add_right
  exact badBiUnionDivisorFilter_sum_le_largeDivisor_sum A x x₀

@[bridge_target_tag]
theorem supportedAboveFinset_mono {x y : ℕ} {A : Finset ℕ}
    (hxy : y ≤ x) (hA : SupportedAboveFinset x A) :
    SupportedAboveFinset y A := by
  intro n hn
  exact le_trans hxy (hA hn)

@[bridge_target_tag]
theorem supportedAbove_mono {x y : ℕ} {A : Set ℕ}
    (hxy : y ≤ x) (hA : SupportedAbove x A) :
    SupportedAbove y A := by
  intro n hn
  exact le_trans hxy (hA hn)

/-!
## Real arithmetic debt: large-divisor slice estimates

The following lemmas state the remaining analytic obligations after the
structural reduction in
`primitiveWeight_vonMangoldt_divisorSigma_scaled_le_largeDivisorSlice_of_finiteStatement`.

### Mathematical context (Lichtman 2022, arXiv:2202.02384)

`PrimitiveSetsAboveFiniteStatement` is the finitary form of the
Erdős–Sárközy–Szemerédi conjecture:
  lim_{x → ∞} sup { f(A) | A primitive, A ⊆ [x, ∞) } ≤ 1
where f(A) = Σ_{a ∈ A} 1/(a log a).
Lichtman (Theorem 1.5) proved the limit is ≤ e^γ · π/4 ≈ 1.399.

The endpoint theorem
`primitiveWeight_vonMangoldt_divisorSigma_scaled_le_largeDivisorSlice_of_finiteStatement`
decomposes the von Mangoldt sigma-sum via:
  Σ_{(a,d) ∈ A.sigma d.divisors} primitiveWeight(a) · Λ(d)          [= Σ_{a ∈ A} 1/a]
  ≤ Σ_{good d ≤ x/x₀} Λ(d) · (w_A(d) + 1 + ε)                    [bootstrap]
  + Σ_{large d > x/x₀} Λ(d) · (w_A(d) + primitiveWeightSum(Q_d\{1}))  [remaining debt]

The "good" part is handled by applying `PrimitiveSetsAboveFiniteStatement`
recursively to the quotient Q_d = {a/d | a ∈ A, d ∣ a}, which is primitive and
supported above x/d ≥ x₀ for d ≤ x/x₀.

The "large" part (d > x/x₀) is the remaining analytic debt. Three connected
lemmas close this gap:

1. `primitiveWeightSum_vonMangoldt_sigma_le_log_mul_add` — the harmonic-sum
   / primitiveWeightSum coupling via Chebyshev's ψ.
2. `largeDivisorVonMangoldt_sum_le_eps` — the large-slice Λ-sum → 0 as
   x → ∞, using Chebyshev bounds.
3. `primitiveWeightSum_le_of_largeDivisorEstimate` — the final assembly:
   `PrimitiveSetsAboveFiniteStatement` from the three pieces above.

### Mathlib availability
The following Mathlib tools are available for these proofs:
- `ArithmeticFunction.vonMangoldt_sum`: Σ_{d∣n} Λ(d) = Real.log n
- `ArithmeticFunction.vonMangoldt_le_log`: Λ(n) ≤ Real.log n
- `ArithmeticFunction.vonMangoldt_nonneg`: 0 ≤ Λ(n)
- `Chebyshev.psi_le_const_mul_self`: ψ(x) ≤ (log 4 + 4) · x  (`Mathlib.NumberTheory.Chebyshev`)
- `Chebyshev.theta_le_log4_mul_x`: θ(x) ≤ log(4) · x
- `Chebyshev.psi_eq_sum_Icc`: ψ(x) = Σ_{n ≤ x} Λ(n)
-/

/--
Coupling lemma: for A primitive and supported above x ≥ 2, the primitiveWeightSum
is bounded in terms of the von Mangoldt sigma-sum divided by log(x).

Concretely, for a ≥ x: primitiveWeight(a) = 1/(a log a) ≤ (1/log x) · (1/a),
so f(A) ≤ (1/log x) · Σ_{a ∈ A} 1/a = (1/log x) · sigma_sum(A).

This lemma bridges the sigma-sum upper bound (established by the structural
reduction) to the primitiveWeightSum bound that `PrimitiveSetsAboveFiniteStatement`
requires.
-/
theorem primitiveWeightSum_le_div_log_mul_sigma
    {A : Finset ℕ} {x : ℕ} (hx : 2 ≤ x)
    (hAsupp : SupportedAboveFinset x A) :
    primitiveWeightSum A
      ≤ (1 / Real.log x)
          * Finset.sum (A.sigma fun a => a.divisors)
              (fun y => primitiveWeight y.1 * realVonMangoldt y.2) := by
  have hx_pos : (0 : ℝ) < ↑x :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hx)
  have hlogx_pos : (0 : ℝ) < Real.log ↑x :=
    Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hx)
  have hlogx_ne : Real.log ↑x ≠ 0 := ne_of_gt hlogx_pos
  have hsigma_eq : Finset.sum (A.sigma fun a => a.divisors)
        (fun y => primitiveWeight y.1 * realVonMangoldt y.2)
      = Finset.sum A (fun a => primitiveWeight a * Real.log ↑a) := by
    rw [← primitiveWeight_vonMangoldt_divisorSigma_eq,
        primitiveWeight_vonMangoldt_divisorSum_eq_log]
  rw [hsigma_eq]
  have key : Real.log ↑x * primitiveWeightSum A ≤
      Finset.sum A (fun a => primitiveWeight a * Real.log ↑a) := by
    unfold primitiveWeightSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    calc Real.log ↑x * primitiveWeight a
        = primitiveWeight a * Real.log ↑x := mul_comm _ _
      _ ≤ primitiveWeight a * Real.log ↑a :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log hx_pos (by exact_mod_cast hAsupp ha))
            (primitiveWeight_nonneg a)
  calc primitiveWeightSum A
      = (Real.log ↑x)⁻¹ * (Real.log ↑x * primitiveWeightSum A) := by
          rw [← mul_assoc, inv_mul_cancel₀ hlogx_ne, one_mul]
    _ ≤ (Real.log ↑x)⁻¹ *
          Finset.sum A (fun a => primitiveWeight a * Real.log ↑a) :=
          mul_le_mul_of_nonneg_left key (inv_pos.mpr hlogx_pos).le
    _ = (1 / Real.log ↑x) *
          Finset.sum A (fun a => primitiveWeight a * Real.log ↑a) := by
          rw [one_div]

/-!
### Analytic debt: the large-divisor lane

The theorem `largeDivisorVonMangoldt_sum_le_eps` (previously drafted here) is
**false** as a uniform bound over all finite primitive sets supported above `x`.

Counterexample: let `A` be any finite set of `k` primes all ≥ x. Then `A` is
primitive. For each `p ∈ A` the only large divisor is `d = p` itself, and
`primitiveDivisorQuotient A p = {1}` (no other prime of `A` is divisible by `p`),
so the quotient term vanishes. The large-divisor sum then contains

  Σ_{p ∈ A} Λ(p) · primitiveWeight p = Σ_{p ∈ A} (log p) / (p · log p) = Σ_{p ∈ A} 1/p.

By choosing `A` large enough, `Σ 1/p` exceeds any fixed `ε` — this follows from
divergence of the prime reciprocal series (`Mathlib.NumberTheory.SumPrimeReciprocals`).

The correct analytic lane must retain the **square** of the logarithm. The primitive
weight `1/(a log a)` arises from the log-squared divisor identity

  1/(a log a) = (1/(a (log a)²)) · Σ_{d | a} Λ(d),

rather than from `(1/a) · Σ_{d | a} Λ(d) / log a` used in the sigma bridge. The
corrected large-divisor estimate should weight terms as `Λ(d) / (d · log d)` so
that the prime diagonal contributes `1/(p log p)`, not `1/p`.

We record the **shape** of the correct analytic input as an opaque `Prop`
placeholder. Downstream propositions that require this estimate should take it as
an explicit hypothesis rather than relying on a false uniform bound.

Two earlier drafts of this `Prop` were also false:

* **First draft** (divisor-only, `Λ(d)/(d log d)` + quotient term): the prime
  diagonal gives `1/p` not `1/(p log p)`, and the quotient term `primitiveWeightSum
  (Q_d \ {1})` is unscaled — its contribution is a fixed positive constant for
  any `d | 2d` (e.g. `A = {2d}` gives quotient `{2}`, contributing `primitiveWeight 2`
  regardless of `x₀`).

* **Second draft** (divisor-only `Λ(d)/(d (log d)²)` + unscaled quotient): same
  quotient defect. The log-squared denominator must be attached to the **original
  element `a`**, not the divisor `d`.

The correct kernel uses the pair `(a, d)` from `A.sigma (fun a => a.divisors)`.
For `a > 1` the log-squared divisor identity `1/(a log a) = (1/(a (log a)²)) * Σ_{d|a} Λ(d)`
shows that the kernel `Λ(d) / (a * (log a)²)` sums to `primitiveWeight a` over all
`d | a`. This ensures the prime diagonal is `1/(p log p)` and all quotient
contributions are scaled by `1/(a (log a)²)`.
-/

/--
Log-squared pair kernel for the exact primitive-weight decomposition.

For `a > 1`, summing `primitiveLogSquaredPairKernel a d` over `d ∈ a.divisors`
recovers `primitiveWeight a`:

  Σ_{d | a} Λ(d) / (a * (log a)²)
    = (1 / (a * (log a)²)) * Σ_{d | a} Λ(d)
    = (1 / (a * (log a)²)) * log a
    = 1 / (a * log a)
    = primitiveWeight a.

On a prime `p`: `Λ(p) / (p * (log p)²) = (log p) / (p * (log p)²) = 1 / (p * log p)`,
matching `primitiveWeight p`. The denominator is in `a`, not `d`, which prevents the
quotient-scaling defect in divisor-only formulations.
-/
def primitiveLogSquaredPairKernel (a d : ℕ) : ℝ :=
  if 1 < a then
    realVonMangoldt d / ((a : ℝ) * (Real.log (a : ℝ)) ^ 2)
  else
    0

/--
Correct analytic input for the large-divisor lane.

The sum is over **divisor pairs** `(a, d)` from `A.sigma (fun a => a.divisors)`,
filtered to large divisors `d > x / x₀`. The kernel `Λ(d) / (a * (log a)²)` is
attached to the original element `a`, not the divisor `d` alone.

This avoids both defects present in divisor-only formulations:
- The prime diagonal: `Λ(p) / (p * (log p)²) = 1/(p log p) = primitiveWeight p`. ✓
- The quotient term is automatically scaled: summing over `d | a` gives
  `primitiveWeight a`, so the contribution from each `a` is bounded by `primitiveWeight a`.

**Not asserted**: we do not claim this is provable from current Mathlib; it is an
owner-surface placeholder recording the correct analytic shape.
-/
def PrimitiveLargeDivisorAnalyticInput : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x₀ : ℕ, ∀ {A : Finset ℕ} {x : ℕ},
      x₀ ≤ x →
      PrimitiveFinset A →
      SupportedAboveFinset x A →
      let largePairs :=
        (A.sigma fun a => a.divisors).filter (fun y => x / x₀ < y.2)
      Finset.sum largePairs (fun y => primitiveLogSquaredPairKernel y.1 y.2) ≤ ε

/--
Assembly statement: the analytic input implies the finite ESS statement.

Kept as a `Prop` (not a `theorem ... := by sorry`) because this module does not
claim the analytic proof. This records the logical dependence without asserting
an unproved or false theorem.
-/
def PrimitiveWeightSumAssemblyFromAnalyticInput : Prop :=
  PrimitiveLargeDivisorAnalyticInput → PrimitiveSetsAboveFiniteStatement

/-
Lichtman–ESS bound: the good-divisor sum is bounded by `(1 + ε) · ψ(x/x₀)`.

For A primitive supported above x, with good divisors defined by
`x₀ ≤ max (x / d) 2`, the hypothesis `2 < x₀` forces `x₀ > 2`, hence the
condition `x₀ ≤ max (x / d) 2` implies `x₀ ≤ x / d` (since `max (x/d) 2 = x₀`
would require `x₀ ≤ 2`, contradiction). So all good `d` satisfy `d ≤ x / x₀ < x`.
Since A is supported above x, no element of A is a good divisor, and the
diagonal term `if d ∈ A then primitiveWeight d else 0` vanishes. What remains is:

  Σ_{good d} Λ(d) · (1 + ε) ≤ (1 + ε) · ψ(x / x₀)
    ≤ (1 + ε) · (log 4 + 4) · (x / x₀)

by `Chebyshev.psi_le_const_mul_self` (from `Mathlib.NumberTheory.Chebyshev`).

**Why `2 < x₀` is needed, not just `0 < x₀`**: with `x₀ ≤ 2`, the filter
condition `x₀ ≤ max (x / d) 2` is satisfied by all `d` (since `max _ 2 ≥ 2 ≥ x₀`),
so the good filter includes `d ∈ A`, the diagonal term is positive, and the
RHS `(x / x₀ : ℕ)` can be zero. Concrete counterexample: `x₀ = 2`, `x = 1`,
`A = {p}` for any prime `p`; LHS > 0 but RHS = (1 / 2 : ℕ) = 0.
-/
/--
Explicit Chebyshev/good-divisor input for the finite primitive-set assembly.

This is deliberately a named proposition, not an axiom.  The theorem
`goodDivisorSumChebyshevBound` below proves it from the local good-divisor
argument and the Mathlib Chebyshev estimate `Chebyshev.psi_le_const_mul_self`.
-/
def GoodDivisorSumChebyshevBound : Prop :=
  ∀ {A : Finset ℕ} {x x₀ : ℕ} {ε : ℝ}, 0 < ε →
    2 < x₀ →
    1 ≤ x →
    PrimitiveFinset A →
    SupportedAboveFinset x A →
    let D := A.biUnion (fun a => a.divisors)
    let good := D.filter (fun d => x₀ ≤ max (x / d) 2)
    Finset.sum good
        (fun d => realVonMangoldt d
          * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε)))
      ≤ (1 + ε) * (Real.log 4 + 4) * (x / x₀ : ℕ)

/--
Chebyshev/good-divisor bound.

This is the formalized local proof route described in the Lichtman--ESS
good-divisor decomposition.  If `d` is good and `2 < x₀`, then
`x₀ ≤ x / d`, hence `d ≤ x / x₀`.  Since `A` is supported above `x`, no such
good divisor can itself lie in `A`; the diagonal term vanishes.  The remaining
sum is bounded by Chebyshev's `ψ(x/x₀)` and then by
`Chebyshev.psi_le_const_mul_self`.
-/
theorem goodDivisorSumChebyshevBound :
    GoodDivisorSumChebyshevBound := by
  intro A x x₀ ε hε hx₀ hx hAprim hAsupp
  let D := A.biUnion (fun a => a.divisors)
  let good := D.filter (fun d => x₀ ≤ max (x / d) 2)
  have hx₀_pos : 0 < x₀ := Nat.lt_trans (by norm_num) hx₀
  have hx₀_one : 1 < x₀ := Nat.lt_trans (by norm_num) hx₀
  have hx_pos : 0 < x := Nat.succ_le_iff.mp hx
  have hgood_le :
      ∀ d ∈ good, d ≤ x / x₀ := by
    intro d hd
    have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
    have hdgood : x₀ ≤ max (x / d) 2 := (Finset.mem_filter.mp hd).2
    rcases Finset.mem_biUnion.mp hdD with ⟨a, haA, hddiv⟩
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hddiv
    have hx₀_le_x_div_d : x₀ ≤ x / d := by
      rcases (le_max_iff.mp hdgood) with hx₀_le | hx₀_le_two
      · exact hx₀_le
      · exact False.elim ((not_le.mpr hx₀) hx₀_le_two)
    have hx₀_mul_d_le_x : x₀ * d ≤ x :=
      (Nat.le_div_iff_mul_le hd_pos).mp hx₀_le_x_div_d
    exact
      (Nat.le_div_iff_mul_le hx₀_pos).mpr
        (by simpa [Nat.mul_comm] using hx₀_mul_d_le_x)
  have hgood_not_mem_A :
      ∀ d ∈ good, d ∉ A := by
    intro d hd hdA
    have hd_le : d ≤ x / x₀ := hgood_le d hd
    have hx_div_lt : x / x₀ < x :=
      Nat.div_lt_self hx_pos hx₀_one
    have hd_lt_x : d < x := lt_of_le_of_lt hd_le hx_div_lt
    have hx_le_d : x ≤ d := hAsupp hdA
    exact (not_lt_of_ge hx_le_d) hd_lt_x
  have hsum_eq :
      Finset.sum good
          (fun d => realVonMangoldt d
            * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε)))
        =
      Finset.sum good (fun d => (1 + ε) * realVonMangoldt d) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdA : d ∉ A := hgood_not_mem_A d hd
    simp [hdA]
    ring
  have hsubset :
      good ⊆ Finset.Icc 0 (x / x₀) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le d, hgood_le d hd⟩
  have hsum_le_icc :
      Finset.sum good realVonMangoldt
        ≤ Finset.sum (Finset.Icc 0 (x / x₀)) realVonMangoldt := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro d _ _
    exact realVonMangoldt_nonneg d
  have hpsi_eq :
      Chebyshev.psi ((x / x₀ : ℕ) : ℝ)
        = Finset.sum (Finset.Icc 0 (x / x₀)) realVonMangoldt := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp [realVonMangoldt]
  have hsum_le_psi :
      Finset.sum good realVonMangoldt
        ≤ Chebyshev.psi ((x / x₀ : ℕ) : ℝ) := by
    simpa [hpsi_eq] using hsum_le_icc
  have hpsi_bound :
      Chebyshev.psi ((x / x₀ : ℕ) : ℝ)
        ≤ (Real.log 4 + 4) * ((x / x₀ : ℕ) : ℝ) :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have hfactor_nonneg : 0 ≤ 1 + ε := by linarith
  calc
    Finset.sum good
        (fun d => realVonMangoldt d
          * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε)))
        = Finset.sum good (fun d => (1 + ε) * realVonMangoldt d) := hsum_eq
    _ = (1 + ε) * Finset.sum good realVonMangoldt := by
      rw [Finset.mul_sum]
    _ ≤ (1 + ε) * Chebyshev.psi ((x / x₀ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hsum_le_psi hfactor_nonneg
    _ ≤ (1 + ε) * ((Real.log 4 + 4) * ((x / x₀ : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hpsi_bound hfactor_nonneg
    _ = (1 + ε) * (Real.log 4 + 4) * (x / x₀ : ℕ) := by
      ring

/--
Good-divisor sum bound, exposed under the original public theorem name.
-/
theorem goodDivisorSum_le_log_mul_add
    {A : Finset ℕ} {x x₀ : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hx₀ : 2 < x₀) (hx : 1 ≤ x)
    (hAprim : PrimitiveFinset A)
    (hAsupp : SupportedAboveFinset x A) :
    let D := A.biUnion (fun a => a.divisors)
    let good := D.filter (fun d => x₀ ≤ max (x / d) 2)
    Finset.sum good
        (fun d => realVonMangoldt d
          * ((if d ∈ A then primitiveWeight d else 0) + (1 + ε)))
      ≤ (1 + ε) * (Real.log 4 + 4) * (x / x₀ : ℕ) :=
  goodDivisorSumChebyshevBound hε hx₀ hx hAprim hAsupp

/-! ## MaxEnt interpretation socket -/

/--
A finite MaxEnt interpretation socket for primitive supports.

This does not assert that primes maximize the primitive weight sum.  It only
packages a model-specific entropy/readout functional and a supplied optimality
law.
-/
structure PrimitiveFiniteMaxEntWitness where
  /-- Candidate finite primitive support. -/
  support :
    Finset ℕ

  /-- Entropy/readout assigned to finite supports. -/
  entropyReadout :
    Finset ℕ → ℝ

  /-- Admissibility predicate, usually primitive plus support bounds. -/
  admissible :
    Finset ℕ → Prop

  /-- The candidate support is admissible. -/
  support_admissible :
    admissible support

  /-- Supplied MaxEnt optimality law. -/
  maxent_law :
    ∀ A : Finset ℕ, admissible A → entropyReadout A ≤ entropyReadout support

namespace PrimitiveFiniteMaxEntWitness

variable (M : PrimitiveFiniteMaxEntWitness)

/-- The supplied MaxEnt candidate is admissible. -/
theorem admissible_valid :
    M.admissible M.support :=
  M.support_admissible

/-- The supplied MaxEnt candidate dominates all admissible finite supports. -/
theorem entropyReadout_le_support
    (A : Finset ℕ)
    (hA : M.admissible A) :
    M.entropyReadout A ≤ M.entropyReadout M.support :=
  M.maxent_law A hA

end PrimitiveFiniteMaxEntWitness

end InfoGeometry.Arithmetic
