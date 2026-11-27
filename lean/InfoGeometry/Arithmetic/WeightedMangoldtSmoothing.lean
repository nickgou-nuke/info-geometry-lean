/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.SmoothedMangoldtGrowth

/-!
# Weighted real Mangoldt smoothing and normalization

For arbitrary real arithmetic coefficients `a`, this owner constructs the
finite real-cutoff smoothing `S_a(x) = Σ_{1 ≤ n ≤ floor x} a(n) (x/n - 1)`.
Its affine interpolation does not require positivity of the coefficients.
Centering by `κ * x * log x - β * x` introduces exactly `κ` times the
existing logarithmic chord error.

Dividing the centered smoothing by a positive cutoff gives the normalized
remainder used by one-sided prime-sum estimates. The power-bound conversion
retains the exponent shift by one. All growth estimates remain explicit
hypotheses; this file proves no arithmetic cancellation or zero exclusion.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.WeightedMangoldtSmoothing

open InfoGeometry.Analysis.CenteredLogInterpolation

/-- Harmonic prefix of arbitrary real arithmetic coefficients. -/
def harmonicPrefix (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)

/-- Unweighted prefix of the same coefficients. -/
def coefficientPrefix (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n

/-- The finite smoothing at a natural cutoff. -/
def finiteSmoothing (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * ((N : ℝ) / (n : ℝ) - 1)

/-- The same smoothing at an arbitrary real cutoff. -/
def smoothing (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / (n : ℝ) - 1)

/-- Normalized finite kernel, before its logarithmic and constant centering. -/
def normalizedSmoothing (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (1 / (n : ℝ) - 1 / x)

/-- Centered smoothing with an explicit logarithmic coefficient and offset. -/
def centeredSmoothing (a : ℕ → ℝ) (κ β x : ℝ) : ℝ :=
  smoothing a x - κ * x * Real.log x + β * x

/-- The normalized centered remainder. -/
def centeredRemainder (a : ℕ → ℝ) (κ β x : ℝ) : ℝ :=
  normalizedSmoothing a x - κ * Real.log x + β

private theorem sum_Icc_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 1), f n) =
      (∑ n ∈ Finset.Icc 1 N, f n) + f (N + 1) := by
  have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  ring

theorem harmonicPrefix_succ (a : ℕ → ℝ) (N : ℕ) :
    harmonicPrefix a (N + 1) =
      harmonicPrefix a N + a (N + 1) / ((N + 1 : ℕ) : ℝ) := by
  exact sum_Icc_succ (fun n => a n / (n : ℝ)) N

theorem coefficientPrefix_succ (a : ℕ → ℝ) (N : ℕ) :
    coefficientPrefix a (N + 1) = coefficientPrefix a N + a (N + 1) := by
  exact sum_Icc_succ a N

theorem finiteSmoothing_eq_harmonic_sub_prefix (a : ℕ → ℝ) (N : ℕ) :
    finiteSmoothing a N = (N : ℝ) * harmonicPrefix a N - coefficientPrefix a N := by
  unfold finiteSmoothing harmonicPrefix coefficientPrefix
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem finiteSmoothing_succ_sub (a : ℕ → ℝ) (N : ℕ) :
    finiteSmoothing a (N + 1) - finiteSmoothing a N = harmonicPrefix a N := by
  rw [finiteSmoothing_eq_harmonic_sub_prefix,
    finiteSmoothing_eq_harmonic_sub_prefix, harmonicPrefix_succ, coefficientPrefix_succ]
  have hcancel : ((N + 1 : ℕ) : ℝ) *
      (a (N + 1) / ((N + 1 : ℕ) : ℝ)) = a (N + 1) := by
    have hN0 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hN0]
  calc
    _ = harmonicPrefix a N + ((N + 1 : ℕ) : ℝ) *
        (a (N + 1) / ((N + 1 : ℕ) : ℝ)) - a (N + 1) := by
      push_cast
      ring
    _ = harmonicPrefix a N := by rw [hcancel]; ring

/-- The second difference recovers the next weighted arithmetic coefficient. -/
theorem finiteSmoothing_second_difference (a : ℕ → ℝ) (N : ℕ) :
    finiteSmoothing a (N + 2) - 2 * finiteSmoothing a (N + 1) +
      finiteSmoothing a N = a (N + 1) / ((N + 1 : ℕ) : ℝ) := by
  have hnext := finiteSmoothing_succ_sub a (N + 1)
  have hprev := finiteSmoothing_succ_sub a N
  have hstep := harmonicPrefix_succ a N
  have hindex : N + 1 + 1 = N + 2 := by omega
  rw [hindex] at hnext
  linarith

@[simp] theorem smoothing_natCast (a : ℕ → ℝ) (N : ℕ) :
    smoothing a (N : ℝ) = finiteSmoothing a N := by
  simp [smoothing, finiteSmoothing]

theorem smoothing_eq_harmonic_sub_prefix (a : ℕ → ℝ) (x : ℝ) :
    smoothing a x = x * harmonicPrefix a ⌊x⌋₊ - coefficientPrefix a ⌊x⌋₊ := by
  unfold smoothing harmonicPrefix coefficientPrefix
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Prefix form of the normalized kernel; this also holds at the totalized value `x = 0`. -/
theorem normalizedSmoothing_eq_harmonic_sub_prefix (a : ℕ → ℝ) (x : ℝ) :
    normalizedSmoothing a x =
      harmonicPrefix a ⌊x⌋₊ - coefficientPrefix a ⌊x⌋₊ / x := by
  unfold normalizedSmoothing harmonicPrefix coefficientPrefix
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem smoothing_eq_floor_affine (a : ℕ → ℝ) (x : ℝ) :
    smoothing a x = finiteSmoothing a ⌊x⌋₊ +
      (x - (⌊x⌋₊ : ℝ)) * harmonicPrefix a ⌊x⌋₊ := by
  rw [smoothing_eq_harmonic_sub_prefix, finiteSmoothing_eq_harmonic_sub_prefix]
  ring

/-- Affine interpolation includes the right endpoint because its new summand vanishes. -/
theorem smoothing_add_unitInterval (a : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    smoothing a ((N : ℝ) + t) = finiteSmoothing a N + t * harmonicPrefix a N := by
  rcases lt_or_eq_of_le ht1 with htlt | rfl
  · have hfloor : ⌊(N : ℝ) + t⌋₊ = N := by
      apply (Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg N) ht0)).2
      constructor <;> linarith
    rw [smoothing_eq_floor_affine, hfloor]
    ring
  · rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by simp,
      smoothing_natCast, one_mul]
    linarith [finiteSmoothing_succ_sub a N]

theorem smoothing_eq_affine (a : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    smoothing a ((N : ℝ) + t) =
      (1 - t) * smoothing a (N : ℝ) + t * smoothing a ((N + 1 : ℕ) : ℝ) := by
  rw [smoothing_add_unitInterval a N t ht0 ht1, smoothing_natCast, smoothing_natCast]
  have hsucc : finiteSmoothing a (N + 1) = finiteSmoothing a N + harmonicPrefix a N := by
    linarith [finiteSmoothing_succ_sub a N]
  rw [hsucc]
  ring

/-- No sign or positivity assumption on `a`, `κ`, or `β` is needed for the identity. -/
theorem centeredSmoothing_eq_affine_add_error (a : ℕ → ℝ) (κ β : ℝ)
    (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    centeredSmoothing a κ β ((N : ℝ) + t) =
      (1 - t) * centeredSmoothing a κ β (N : ℝ) +
        t * centeredSmoothing a κ β ((N + 1 : ℕ) : ℝ) +
          κ * logChordError (N : ℝ) t := by
  unfold centeredSmoothing
  rw [smoothing_eq_affine a N t ht0 ht1]
  unfold logChordError
  push_cast
  ring

/-- For either fixed sign, a nonnegative logarithmic coefficient controls the chord loss. -/
theorem signed_centeredSmoothing_le_affine (a : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (β : ℝ) {N : ℕ} (hN : 1 ≤ N) {sign : ℝ}
    (hsign : sign = 1 ∨ sign = -1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sign * centeredSmoothing a κ β ((N : ℝ) + t) ≤
      (1 - t) * (sign * centeredSmoothing a κ β (N : ℝ)) +
        t * (sign * centeredSmoothing a κ β ((N + 1 : ℕ) : ℝ)) +
          κ / (8 * (N : ℝ)) := by
  have herror := logChordError_nat_bounds hN ht0 ht1
  have herror0 : 0 ≤ κ * logChordError (N : ℝ) t := mul_nonneg hκ herror.1
  have herrorUpper : κ * logChordError (N : ℝ) t ≤ κ / (8 * (N : ℝ)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left herror.2 hκ
  have hbound0 : 0 ≤ κ / (8 * (N : ℝ)) := by positivity
  rw [centeredSmoothing_eq_affine_add_error a κ β N t ht0 ht1]
  rcases hsign with rfl | rfl <;> nlinarith

/-- The finite kernels differ by precisely a factor of the nonzero cutoff. -/
theorem smoothing_div_eq_normalizedSmoothing (a : ℕ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    smoothing a x / x = normalizedSmoothing a x := by
  unfold smoothing normalizedSmoothing
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  field_simp [hx, hn0]

/-- This is the normalization needed by the external twisted prime remainder. -/
theorem centeredSmoothing_div_eq_centeredRemainder
    (a : ℕ → ℝ) (κ β x : ℝ) (hx : x ≠ 0) :
    centeredSmoothing a κ β x / x = centeredRemainder a κ β x := by
  unfold centeredSmoothing centeredRemainder
  rw [add_div, sub_div, smoothing_div_eq_normalizedSmoothing a x hx]
  field_simp [hx]

/-- Multiplication by a positive cutoff shifts the power exponent by one. -/
theorem centeredSmoothing_power_bound_iff
    (a : ℕ → ℝ) (κ β sign C alpha x : ℝ) (hx : 0 < x) :
    sign * centeredSmoothing a κ β x ≤ C * x ^ alpha ↔
      sign * centeredRemainder a κ β x ≤ C * x ^ (alpha - 1) := by
  have hnorm : centeredSmoothing a κ β x = centeredRemainder a κ β x * x :=
    (div_eq_iff hx.ne').mp (centeredSmoothing_div_eq_centeredRemainder a κ β x hx.ne')
  have hpow : x ^ (alpha - 1) * x = x ^ alpha := by
    calc
      x ^ (alpha - 1) * x = x ^ (alpha - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((alpha - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = x ^ alpha := by congr 1; ring
  have hleft : (sign * centeredRemainder a κ β x) * x =
      sign * centeredSmoothing a κ β x := by rw [hnorm]; ring
  have hright : (C * x ^ (alpha - 1)) * x = C * x ^ alpha := by
    rw [mul_assoc, hpow]
  constructor
  · intro h
    apply (mul_le_mul_iff_left₀ hx).mp
    rw [hleft, hright]
    exact h
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h hx.le
    rwa [hleft, hright] at hmul

/-- Recover the existing untwisted real smoothing from the general coefficients. -/
theorem smoothing_vonMangoldt (x : ℝ) :
    smoothing ArithmeticFunction.vonMangoldt x =
      PrimeDistributionLaw.realSmoothedMangoldtSum x := by
  rw [PrimeDistributionLaw.realSmoothedMangoldtSum_eq_Icc]
  rfl

/-- The existing centered Mangoldt owner is exactly the `κ = 1` specialization. -/
theorem centeredSmoothing_vonMangoldt (x : ℝ) :
    centeredSmoothing ArithmeticFunction.vonMangoldt 1
      (1 + Real.eulerMascheroniConstant) x =
        PrimeDistributionLaw.centeredSmoothedMangoldtSum x := by
  simp only [centeredSmoothing, PrimeDistributionLaw.centeredSmoothedMangoldtSum,
    smoothing_vonMangoldt, one_mul]

/-- An eventual fixed-sign power bound at integer cutoffs. -/
def IntegerCenteredPowerBound (a : ℕ → ℝ) (κ β sign alpha : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N →
      sign * centeredSmoothing a κ β (N : ℝ) ≤ C * (N : ℝ) ^ alpha

/-- The corresponding real-cutoff bound. -/
def RealCenteredPowerBound (a : ℕ → ℝ) (κ β sign alpha : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℝ, 1 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → sign * centeredSmoothing a κ β x ≤ C * x ^ alpha

/-- The corresponding bound on the normalized remainder. -/
def RealRemainderPowerBound (a : ℕ → ℝ) (κ β sign exponent : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℝ, 1 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → sign * centeredRemainder a κ β x ≤ C * x ^ exponent

/-- Transfer an integer bound to real cutoffs while retaining the logarithmic scale. -/
theorem centeredSmoothing_real_bound_of_integer_bound
    (a : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ)
    {sign alpha C : ℝ} (hsign : sign = 1 ∨ sign = -1)
    (halpha : 0 ≤ alpha) (hC : 0 ≤ C) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hbound : ∀ N : ℕ, N₀ ≤ N →
      sign * centeredSmoothing a κ β (N : ℝ) ≤ C * (N : ℝ) ^ alpha)
    {x : ℝ} (hx : (N₀ : ℝ) ≤ x) :
    sign * centeredSmoothing a κ β x ≤
      ((2 : ℝ) ^ alpha * C + κ / 8) * x ^ alpha := by
  let N : ℕ := ⌊x⌋₊
  let t : ℝ := x - (N : ℝ)
  have hN₀real : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hx1 : 1 ≤ x := hN₀real.trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hNlarge : N₀ ≤ N := Nat.le_floor hx
  have hN : 1 ≤ N := hN₀.trans hNlarge
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have ht0 : 0 ≤ t := sub_nonneg.mpr hNx
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpoint : (N : ℝ) + t = x := by dsimp [t]; ring
  have hnext : ((N + 1 : ℕ) : ℝ) ≤ 2 * x := by push_cast; linarith
  have hpowN : (N : ℝ) ^ alpha ≤ (2 * x) ^ alpha :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) halpha
  have hpowNext : (((N + 1 : ℕ) : ℝ)) ^ alpha ≤ (2 * x) ^ alpha :=
    Real.rpow_le_rpow (Nat.cast_nonneg (N + 1)) hnext halpha
  have hleft : sign * centeredSmoothing a κ β (N : ℝ) ≤ C * (2 * x) ^ alpha :=
    (hbound N hNlarge).trans (mul_le_mul_of_nonneg_left hpowN hC)
  have hright : sign * centeredSmoothing a κ β ((N + 1 : ℕ) : ℝ) ≤
      C * (2 * x) ^ alpha :=
    (hbound (N + 1) (hNlarge.trans (Nat.le_succ N))).trans
      (mul_le_mul_of_nonneg_left hpowNext hC)
  have haffine : (1 - t) * (sign * centeredSmoothing a κ β (N : ℝ)) +
        t * (sign * centeredSmoothing a κ β ((N + 1 : ℕ) : ℝ)) ≤
      C * (2 * x) ^ alpha := by
    calc
      _ ≤ (1 - t) * (C * (2 * x) ^ alpha) + t * (C * (2 * x) ^ alpha) :=
        add_le_add (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left hright ht0)
      _ = C * (2 * x) ^ alpha := by ring
  have herror : κ / (8 * (N : ℝ)) ≤ (κ / 8) * x ^ alpha := by
    have hbase : 1 / (8 * (N : ℝ)) ≤ (1 / 8 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hbase' : κ / (8 * (N : ℝ)) ≤ κ / 8 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hbase hκ
    calc
      _ ≤ κ / 8 := hbase'
      _ ≤ (κ / 8) * x ^ alpha := by
        have h := mul_le_mul_of_nonneg_left (Real.one_le_rpow hx1 halpha)
          (by positivity : 0 ≤ κ / 8)
        simpa using h
  have hinterp := signed_centeredSmoothing_le_affine a hκ β hN hsign t ht0 ht1
  rw [hpoint] at hinterp
  calc
    sign * centeredSmoothing a κ β x ≤ C * (2 * x) ^ alpha + κ / (8 * (N : ℝ)) :=
      hinterp.trans (add_le_add haffine le_rfl)
    _ ≤ C * (2 * x) ^ alpha + (κ / 8) * x ^ alpha := add_le_add le_rfl herror
    _ = ((2 : ℝ) ^ alpha * C + κ / 8) * x ^ alpha := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0]
      ring

theorem realCenteredPowerBound_of_integer
    (a : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {sign alpha : ℝ}
    (hsign : sign = 1 ∨ sign = -1) (halpha : 0 ≤ alpha)
    (h : IntegerCenteredPowerBound a κ β sign alpha) :
    RealCenteredPowerBound a κ β sign alpha := by
  obtain ⟨C, hC, N₀, hN₀, hbound⟩ := h
  refine ⟨(2 : ℝ) ^ alpha * C + κ / 8, by positivity, (N₀ : ℝ), ?_, ?_⟩
  · exact_mod_cast hN₀
  · intro x hx
    exact centeredSmoothing_real_bound_of_integer_bound a hκ β
      hsign halpha hC hN₀ hbound hx

theorem integerCenteredPowerBound_of_real
    (a : ℕ → ℝ) (κ β sign alpha : ℝ)
    (h : RealCenteredPowerBound a κ β sign alpha) :
    IntegerCenteredPowerBound a κ β sign alpha := by
  obtain ⟨C, hC, x₀, hx₀, hbound⟩ := h
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge x₀
  refine ⟨C, hC, N₀, ?_, ?_⟩
  · exact_mod_cast hx₀.trans hN₀
  · intro N hN
    exact hbound (N : ℝ) (hN₀.trans (by exact_mod_cast hN))

theorem integerCenteredPowerBound_iff_real
    (a : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {sign alpha : ℝ}
    (hsign : sign = 1 ∨ sign = -1) (halpha : 0 ≤ alpha) :
    IntegerCenteredPowerBound a κ β sign alpha ↔ RealCenteredPowerBound a κ β sign alpha :=
  ⟨realCenteredPowerBound_of_integer a hκ β hsign halpha,
    integerCenteredPowerBound_of_real a κ β sign alpha⟩

/-- The same constants and thresholds work after the exact exponent shift. -/
theorem realCenteredPowerBound_iff_remainder
    (a : ℕ → ℝ) (κ β sign alpha : ℝ) :
    RealCenteredPowerBound a κ β sign alpha ↔
      RealRemainderPowerBound a κ β sign (alpha - 1) := by
  constructor
  · rintro ⟨C, hC, x₀, hx₀, hbound⟩
    refine ⟨C, hC, x₀, hx₀, ?_⟩
    intro x hx
    exact (centeredSmoothing_power_bound_iff a κ β sign C alpha x
      (lt_of_lt_of_le zero_lt_one (hx₀.trans hx))).mp (hbound x hx)
  · rintro ⟨C, hC, x₀, hx₀, hbound⟩
    refine ⟨C, hC, x₀, hx₀, ?_⟩
    intro x hx
    exact (centeredSmoothing_power_bound_iff a κ β sign C alpha x
      (lt_of_lt_of_le zero_lt_one (hx₀.trans hx))).mpr (hbound x hx)

/-- Integer smoothing bounds and normalized real bounds express the same hypothesis. -/
theorem integerCenteredPowerBound_iff_remainder
    (a : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {sign alpha : ℝ}
    (hsign : sign = 1 ∨ sign = -1) (halpha : 0 ≤ alpha) :
    IntegerCenteredPowerBound a κ β sign alpha ↔
      RealRemainderPowerBound a κ β sign (alpha - 1) :=
  (integerCenteredPowerBound_iff_real a hκ β hsign halpha).trans
    (realCenteredPowerBound_iff_remainder a κ β sign alpha)

/-- A fixed-sign square-root-plus-epsilon hypothesis at integer cutoffs. -/
def IntegerCenteredSqrtBound (a : ℕ → ℝ) (κ β sign : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → IntegerCenteredPowerBound a κ β sign ((1 : ℝ) / 2 + ε)

/-- The corresponding normalized remainder hypothesis on real cutoffs. -/
def RealRemainderSqrtBound (a : ℕ → ℝ) (κ β sign : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → RealRemainderPowerBound a κ β sign (ε - (1 : ℝ) / 2)

/-- The sign is fixed before epsilon is quantified; normalizing lowers the exponent by one. -/
theorem integerCenteredSqrtBound_iff_remainder
    (a : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (β : ℝ) {sign : ℝ}
    (hsign : sign = 1 ∨ sign = -1) :
    IntegerCenteredSqrtBound a κ β sign ↔ RealRemainderSqrtBound a κ β sign := by
  constructor
  · intro h ε hε
    have hα : 0 ≤ (1 : ℝ) / 2 + ε := by linarith
    have hshift : (1 : ℝ) / 2 + ε - 1 = ε - (1 : ℝ) / 2 := by ring
    simpa only [hshift] using
      (integerCenteredPowerBound_iff_remainder a hκ β hsign hα).mp (h ε hε)
  · intro h ε hε
    have hα : 0 ≤ (1 : ℝ) / 2 + ε := by linarith
    have hshift : (1 : ℝ) / 2 + ε - 1 = ε - (1 : ℝ) / 2 := by ring
    apply (integerCenteredPowerBound_iff_remainder a hκ β hsign hα).mpr
    simpa only [hshift] using h ε hε

end InfoGeometry.Arithmetic.WeightedMangoldtSmoothing
