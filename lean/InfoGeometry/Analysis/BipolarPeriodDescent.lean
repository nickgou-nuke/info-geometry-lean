import InfoGeometry.Analysis.BipolarWindingPeriodLattice
import InfoGeometry.Analysis.CauchyResidueWindingBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Bipolar period image and exponential descent

The repository's canonical Möbius coordinate is `q(s)=s/(1-s)`.  The alternative
coordinate `s/(s-1)` differs from it by the constant factor `-1`, so both carry
the same logarithmic differential

`dq/q = ds/s - ds/(s-1)`.

The source winding carrier remains `ℤ × ℤ`.  The residue-difference form maps it
onto the one-dimensional period image `2πiℤ` and has diagonal kernel.  This file
proves that exact image/kernel statement and then constructs the genuine
quotient descent of the complex exponential.

The elementary circle calculation below certifies the local `2πi` period of a
single Cauchy pole.  It is not promoted to a classification of all continuous
loops in the punctured plane; that would require a separate homology or winding
number theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarPeriodDescent

open Complex Real intervalIntegral
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.CauchyWinding

/-- The sign-shifted Möbius coordinate used in the informal stream. -/
def signedCrossRatio01 (s : ℂ) : ℂ :=
  -crossRatio01 s

/-- Away from the pole, the sign-shifted canonical coordinate is exactly
`s/(s-1)`. -/
theorem signedCrossRatio01_eq_div
    {s : ℂ} (hs : s ∈ punctured01) :
    signedCrossRatio01 s = s / (s - 1) := by
  have h₁ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  have h₂ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  change -(s / (1 - s)) = s / (s - 1)
  field_simp [h₁, h₂]
  ring

/-- The sign shift does not change the nonvanishing locus. -/
theorem signedCrossRatio01_ne_zero
    {s : ℂ} (hs : s ∈ punctured01) :
    signedCrossRatio01 s ≠ 0 := by
  exact neg_ne_zero.mpr (crossRatio01_ne_zero hs)

/-- Derivative of the sign-shifted coordinate `s/(s-1)`. -/
theorem hasDerivAt_signedCrossRatio01
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt signedCrossRatio01 (-1 / (s - 1) ^ 2) s := by
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  convert (hasDerivAt_crossRatio01 hs.2).neg using 1
  field_simp [h₁]
  ring

/-- Both sign conventions have the same logarithmic derivative. -/
theorem signedCrossRatio01_logarithmicDerivative
    {s : ℂ} (hs : s ∈ punctured01) :
    (-1 / (s - 1) ^ 2) / signedCrossRatio01 s = dlog01 s := by
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  rw [signedCrossRatio01_eq_div hs, dlog01_eq_one_div_mul hs]
  have h₂ : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  field_simp [hs.1, h₁, h₂]
  ring

/-- Counterclockwise circle parameterization around `c`. -/
def circleParam (c : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  c + (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))

/-- Velocity assigned to the standard circle parameterization. -/
def circleVelocity (r : ℝ) (t : ℝ) : ℂ :=
  Complex.I * (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))

/-- Pullback coefficient of the Cauchy pole along a nondegenerate positively
oriented circle. -/
def circlePolePullback (c : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  circleVelocity r t / (circleParam c r t - c)

/-- The pullback of `(z-c)⁻¹ dz` is the constant coefficient `i`. -/
theorem circlePolePullback_eq_I
    {c : ℂ} {r : ℝ} (hr : 0 < r) (t : ℝ) :
    circlePolePullback c r t = Complex.I := by
  change
    (Complex.I * (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))) /
      ((r : ℂ) * Complex.exp (Complex.I * (t : ℂ))) = Complex.I
  exact circle_log_deriv_quotient r hr t

/-- Genuine interval-integral evaluation of the elementary Cauchy pole. -/
theorem intervalIntegral_circlePolePullback
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circlePolePullback c r t) =
      (2 * (Real.pi : ℂ) * Complex.I : ℂ) := by
  have hfun :
      (fun t : ℝ => circlePolePullback c r t) = fun _ => Complex.I := by
    funext t
    exact circlePolePullback_eq_I hr t
  rw [hfun]
  exact circle_pole_integral

/-- Predicate for the image lattice `2πiℤ` inside `ℂ`. -/
def IsTwoPiIPeriod (z : ℂ) : Prop :=
  ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * Complex.I : ℂ)

/-- Every bipolar winding period lies in `2πiℤ`. -/
theorem circulationPeriod_isTwoPiIPeriod (w : WindingPair) :
    IsTwoPiIPeriod (circulationPeriod w) := by
  exact ⟨residueWinding w, rfl⟩

/-- Every element of `2πiℤ` is realized by an origin winding. -/
theorem everyTwoPiIPeriod_is_circulationPeriod (k : ℤ) :
    circulationPeriod (k, 0) =
      (k : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
  simp [circulationPeriod, residueWinding]

/-- Exact characterization of the image of the period map. -/
theorem mem_circulationPeriod_range_iff (z : ℂ) :
    (∃ w : WindingPair, circulationPeriod w = z) ↔ IsTwoPiIPeriod z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact circulationPeriod_isTwoPiIPeriod w
  · rintro ⟨k, rfl⟩
    exact ⟨(k, 0), everyTwoPiIPeriod_is_circulationPeriod k⟩

lemma twoPiI_ne_zero :
    (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  refine mul_ne_zero ?_ Complex.I_ne_zero
  exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)

/-- The kernel of the residue-difference period map is exactly the diagonal
subgroup of `ℤ × ℤ`. -/
theorem circulationPeriod_eq_zero_iff (w : WindingPair) :
    circulationPeriod w = 0 ↔ w.1 = w.2 := by
  constructor
  · intro h
    have hcast : (residueWinding w : ℂ) = 0 := by
      exact (mul_eq_zero.mp h).resolve_right twoPiI_ne_zero
    have hint : residueWinding w = 0 := by
      exact_mod_cast hcast
    exact sub_eq_zero.mp hint
  · intro h
    simp [circulationPeriod, residueWinding, h]

/-- Additivity in native product-group notation. -/
theorem circulationPeriod_add_pair (u v : WindingPair) :
    circulationPeriod (u + v) = circulationPeriod u + circulationPeriod v := by
  rcases u with ⟨u₀, u₁⟩
  rcases v with ⟨v₀, v₁⟩
  simpa using circulationPeriod_add (u₀, u₁) (v₀, v₁)

/-- Negating a winding negates its period. -/
theorem circulationPeriod_neg (w : WindingPair) :
    circulationPeriod (-w) = -circulationPeriod w := by
  rcases w with ⟨m, n⟩
  simp [circulationPeriod, residueWinding]
  push_cast
  ring

/-- Two logarithmic potential values are period-equivalent when their
difference is detected by the explicit bipolar winding carrier. -/
def PeriodEquivalent (W₁ W₂ : ℂ) : Prop :=
  ∃ w : WindingPair, W₁ - W₂ = circulationPeriod w

@[refl] theorem PeriodEquivalent.refl (W : ℂ) :
    PeriodEquivalent W W := by
  refine ⟨0, ?_⟩
  simp [circulationPeriod, residueWinding]

@[symm] theorem PeriodEquivalent.symm
    {W₁ W₂ : ℂ} (h : PeriodEquivalent W₁ W₂) :
    PeriodEquivalent W₂ W₁ := by
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, ?_⟩
  rw [circulationPeriod_neg]
  calc
    W₂ - W₁ = -(W₁ - W₂) := by ring
    _ = -circulationPeriod w := by rw [hw]

@[trans] theorem PeriodEquivalent.trans
    {W₁ W₂ W₃ : ℂ}
    (h₁₂ : PeriodEquivalent W₁ W₂)
    (h₂₃ : PeriodEquivalent W₂ W₃) :
    PeriodEquivalent W₁ W₃ := by
  obtain ⟨u, hu⟩ := h₁₂
  obtain ⟨v, hv⟩ := h₂₃
  refine ⟨u + v, ?_⟩
  rw [circulationPeriod_add_pair]
  calc
    W₁ - W₃ = (W₁ - W₂) + (W₂ - W₃) := by ring
    _ = circulationPeriod u + circulationPeriod v := by rw [hu, hv]

/-- The exponential kills every period in the residue-difference image. -/
theorem exp_circulationPeriod (w : WindingPair) :
    Complex.exp (circulationPeriod w) = 1 := by
  simpa [circulationPeriod] using
    Complex.exp_int_mul_two_pi_mul_I (residueWinding w)

/-- Exponentiation is invariant under bipolar period equivalence. -/
theorem exp_eq_of_PeriodEquivalent
    {W₁ W₂ : ℂ} (h : PeriodEquivalent W₁ W₂) :
    Complex.exp W₁ = Complex.exp W₂ := by
  obtain ⟨w, hw⟩ := h
  have hsum : W₁ = W₂ + circulationPeriod w := by
    linear_combination hw
  rw [hsum, Complex.exp_add, exp_circulationPeriod, mul_one]

/-- Because the period map is onto `2πiℤ`, bipolar period equivalence is exactly
the fiber relation of the complex exponential. -/
theorem PeriodEquivalent_iff_exp_eq (W₁ W₂ : ℂ) :
    PeriodEquivalent W₁ W₂ ↔ Complex.exp W₁ = Complex.exp W₂ := by
  constructor
  · exact exp_eq_of_PeriodEquivalent
  · intro h
    rw [Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨(k, 0), ?_⟩
    have hdiff :
        W₁ - W₂ = (k : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
      linear_combination hk
    simpa [circulationPeriod, residueWinding] using hdiff

/-- Setoid of logarithmic potentials modulo the bipolar period image. -/
def periodSetoid : Setoid ℂ where
  r := PeriodEquivalent
  iseqv := ⟨PeriodEquivalent.refl, PeriodEquivalent.symm,
    PeriodEquivalent.trans⟩

/-- Quotient carrier for multi-valued logarithmic potentials. -/
abbrev LogPotentialQuotient := Quotient periodSetoid

/-- The complex exponential genuinely descends through the period quotient. -/
def descendedExp : LogPotentialQuotient → ℂ :=
  Quotient.lift Complex.exp (fun _ _ h => exp_eq_of_PeriodEquivalent h)

@[simp] theorem descendedExp_mk (W : ℂ) :
    descendedExp (Quotient.mk _ W) = Complex.exp W := rfl

/-- Compact image/kernel/descent packet. -/
theorem bipolar_period_descent_packet (w : WindingPair) (W₁ W₂ : ℂ) :
    IsTwoPiIPeriod (circulationPeriod w) ∧
      (circulationPeriod w = 0 ↔ w.1 = w.2) ∧
      (PeriodEquivalent W₁ W₂ ↔ Complex.exp W₁ = Complex.exp W₂) := by
  exact ⟨circulationPeriod_isTwoPiIPeriod w,
    circulationPeriod_eq_zero_iff w,
    PeriodEquivalent_iff_exp_eq W₁ W₂⟩

end InfoGeometry.Analysis.BipolarPeriodDescent
