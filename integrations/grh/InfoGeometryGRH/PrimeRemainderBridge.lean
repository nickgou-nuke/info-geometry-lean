/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.WeightedMangoldtSmoothing
import New.Reduction.OneSidedBound

/-!
# The exact weighted smoothing used by the pinned GRH proof

The coefficient function is the external proof's actual
`New.lambdaKResidueClass d q`, not the untwisted von Mangoldt function.
The logarithmic coefficient is `1 / Nat.totient q`, and the affine offset
is the negative of `(New.logDerivMean d q 1).re`.

For these parameters the native centered smoothing divided by the positive
cutoff is exactly `New.primeRemainder`.  Consequently the external proved
one-sided estimate supplies an unconditional bound on this concrete native
smoothing.  The Mellin integral and its integrability are transported by the
actual exponential change of variables, with exponent `-s - 1`.
-/

noncomputable section

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace InfoGeometry.GRHIntegration

open InfoGeometry.Arithmetic.WeightedMangoldtSmoothing

/-- The native finite kernel is exactly the difference of the two weighted
partial sums occurring in the external remainder. -/
theorem normalizedSmoothing_eq_lambdaKSum_sub (d : ℕ) [Fact d.Prime]
    (q : ℕ) (x : ℝ) (hx : x ≠ 0) :
    normalizedSmoothing (New.lambdaKResidueClass d q) x =
      New.lambdaKSum d q 0 x - New.lambdaKSum d q 1 x := by
  classical
  unfold normalizedSmoothing New.lambdaKSum
  simp only [pow_zero, mul_one, div_one, pow_one, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
  have hnzero : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  field_simp [hx, hnzero] <;> ring

/-- The centering constant and the residue-class density agree exactly with
the external arithmetic remainder. -/
theorem centeredRemainder_eq_primeRemainder (d : ℕ) [Fact d.Prime]
    (q : ℕ) [NeZero q] (x : ℝ) (hx : x ≠ 0) :
    centeredRemainder (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) x = New.primeRemainder d q x := by
  unfold centeredRemainder New.primeRemainder
  rw [normalizedSmoothing_eq_lambdaKSum_sub d q x hx]
  simp only [div_eq_mul_inv]
  ring

/-- The normalization bridge has no asymptotic hypothesis. -/
theorem centeredSmoothing_div_eq_primeRemainder (d : ℕ) [Fact d.Prime]
    (q : ℕ) [NeZero q] (x : ℝ) (hx : x ≠ 0) :
    centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) x / x = New.primeRemainder d q x := by
  rw [centeredSmoothing_div_eq_centeredRemainder _ _ _ _ hx,
    centeredRemainder_eq_primeRemainder d q x hx]

/-- Multiplying the exact normalized identity recovers the original smoothing. -/
theorem centeredSmoothing_eq_mul_primeRemainder (d : ℕ) [Fact d.Prime]
    (q : ℕ) [NeZero q] (x : ℝ) (hx : x ≠ 0) :
    centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) x = x * New.primeRemainder d q x := by
  simpa only [mul_comm] using
    (div_eq_iff hx).mp (centeredSmoothing_div_eq_primeRemainder d q x hx)

/-- The actual external arithmetic bound, transported to the native weighted
smoothing.  There is no assumed cancellation estimate in this statement. -/
theorem eventually_centeredSmoothing_le_rpow {q : ℕ} [NeZero q]
    (hq : 18480 ∣ q) {d : ℕ} [Fact d.Prime]
    (hd : d ≡ q / 2 - 1 [MOD q]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) x ≤ x ^ (1 / 2 + ε) := by
  filter_upwards [New.eventually_primeRemainder_le_rpow hq hd hε,
    eventually_gt_atTop (0 : ℝ)] with x hbound hx
  rw [centeredSmoothing_eq_mul_primeRemainder d q x hx.ne']
  calc
    x * New.primeRemainder d q x ≤ x * x ^ (-1 / 2 + ε) :=
      mul_le_mul_of_nonneg_left hbound hx.le
    _ = x ^ ((1 : ℝ) + (-1 / 2 + ε)) := by
      rw [Real.rpow_add hx, Real.rpow_one]
    _ = x ^ (1 / 2 + ε) := by congr 1; ring

/-- The external estimate discharges the native real-cutoff growth predicate
for the actual residue-class and quadratic-twist coefficients. -/
theorem weightedMangoldt_realRemainderSqrtBound {q : ℕ} [NeZero q]
    (hq : 18480 ∣ q) {d : ℕ} [Fact d.Prime]
    (hd : d ≡ q / 2 - 1 [MOD q]) :
    RealRemainderSqrtBound (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
      (-(New.logDerivMean d q 1).re) 1 := by
  intro ε hε
  obtain ⟨x₀, hbound⟩ :=
    eventually_atTop.1 (New.eventually_primeRemainder_le_rpow hq hd hε)
  refine ⟨1, zero_le_one, max 1 x₀, le_max_left _ _, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_left 1 x₀).trans hx)
  rw [one_mul, one_mul, centeredRemainder_eq_primeRemainder d q x hxpos.ne']
  have hexp : (-1 / 2 : ℝ) + ε = ε - 1 / 2 := by ring
  simpa only [hexp] using hbound x ((le_max_right 1 x₀).trans hx)

/-- The integer-cutoff predicate is discharged through the existing native
interpolation and normalization equivalence. -/
theorem weightedMangoldt_integerCenteredSqrtBound {q : ℕ} [NeZero q]
    (hq : 18480 ∣ q) {d : ℕ} [Fact d.Prime]
    (hd : d ≡ q / 2 - 1 [MOD q]) :
    IntegerCenteredSqrtBound (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
      (-(New.logDerivMean d q 1).re) 1 := by
  apply (integerCenteredSqrtBound_iff_remainder (New.lambdaKResidueClass d q)
    (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))
    (-(New.logDerivMean d q 1).re) (Or.inl rfl)).mpr
  exact weightedMangoldt_realRemainderSqrtBound hq hd

private theorem exp_smul_mellin_kernel (G : ℝ → ℝ) (s : ℂ) (v : ℝ) :
    Real.exp v • ((G (Real.exp v) : ℂ) * (Real.exp v : ℂ) ^ (-s - 1)) =
      ((G (Real.exp v) / Real.exp v : ℝ) : ℂ) *
        Complex.exp ((1 - s) * (v : ℂ)) := by
  have hx : (Real.exp v : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero v
  have hlog : Complex.log (Real.exp v : ℂ) = (v : ℂ) := by
    rw [Complex.ofReal_exp]
    apply Complex.log_exp
    · simpa using (neg_lt_zero.mpr Real.pi_pos)
    · simpa using Real.pi_pos.le
  have hpower : (Real.exp v : ℂ) ^ (-s) = Complex.exp (-s * (v : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hx, hlog]
    congr 1
    ring
  rw [Complex.cpow_sub (-s) 1 hx, Complex.cpow_one, hpower,
    Complex.real_smul, Complex.ofReal_div]
  rw [show (1 - s) * (v : ℂ) = (v : ℂ) + (-s * (v : ℂ)) by ring,
    Complex.exp_add, ← Complex.ofReal_exp]
  field_simp [hx] <;> ring

/-- The `x = exp v` change of variables fixes the Mellin normalization.
Integrability is supplied separately for the arithmetic specialization below. -/
theorem mellin_eq_normalized_laplace (G : ℝ → ℝ) (s : ℂ) :
    (∫ x : ℝ in Ioi 1, (G x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      ∫ v : ℝ in Ioi 0, ((G (Real.exp v) / Real.exp v : ℝ) : ℂ) *
        Complex.exp ((1 - s) * (v : ℂ)) := by
  calc
    _ = ∫ v : ℝ in Ioi 0,
        Real.exp v • ((G (Real.exp v) : ℂ) * (Real.exp v : ℂ) ^ (-s - 1)) := by
      simpa only [Real.exp_zero] using
        (integral_comp_exp_Ioi (fun x : ℝ => (G x : ℂ) * (x : ℂ) ^ (-s - 1)) 0).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _hv
      exact exp_smul_mellin_kernel G s v

/-- The native weighted Mellin integrand is genuinely integrable in the
half-plane where the external proof computes its transform. -/
theorem integrableOn_centeredSmoothing_mellin (d : ℕ) [Fact d.Prime]
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ =>
      (centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  let G : ℝ → ℝ := centeredSmoothing (New.lambdaKResidueClass d q)
    (Nat.totient q : ℝ)⁻¹ (-(New.logDerivMean d q 1).re)
  have hR : IntegrableOn (fun v : ℝ =>
      (New.primeRemainder d q (Real.exp v) : ℂ) *
        Complex.exp ((1 - s) * (v : ℂ))) (Ioi 0) :=
    New.integrableOn_laplace_of_abs_le
      (by fun_prop [New.primeRemainder, New.lambdaKSum])
      (fun v hv => New.abs_primeRemainder_exp_le d q hv) hs
  have hsub : (fun v : ℝ =>
      Real.exp v • ((G (Real.exp v) : ℂ) * (Real.exp v : ℂ) ^ (-s - 1))) =
      (fun v : ℝ => (New.primeRemainder d q (Real.exp v) : ℂ) *
        Complex.exp ((1 - s) * (v : ℂ))) := by
    funext v
    rw [exp_smul_mellin_kernel]
    congr 1
    exact congrArg (fun t : ℝ => (t : ℂ))
      (centeredSmoothing_div_eq_primeRemainder d q (Real.exp v) (Real.exp_ne_zero v))
  have hint : IntegrableOn (fun v : ℝ =>
      Real.exp v • ((G (Real.exp v) : ℂ) * (Real.exp v : ℂ) ^ (-s - 1))) (Ioi 0) := by
    rw [hsub]
    exact hR
  simpa only [Real.exp_zero] using
    (integrableOn_comp_exp_Ioi (fun x : ℝ => (G x : ℂ) * (x : ℂ) ^ (-s - 1)) 0).mp hint

/-- The concrete native weighted smoothing has exactly the logarithmic-
derivative Mellin transform used by the GRH reduction. -/
theorem integral_centeredSmoothing_mellin (d : ℕ) [Fact d.Prime]
    (q : ℕ) [NeZero q] (hd : d ≠ 2) (hcop : q.Coprime d)
    {s : ℂ} (hs : 2 < s.re) :
    (∫ x : ℝ in Ioi 1,
      (centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (New.logDerivMean d q s / s - ((New.logDerivMean d q 1).re : ℂ)) / (s - 1) := by
  rw [mellin_eq_normalized_laplace]
  calc
    _ = ∫ v : ℝ in Ioi 0, (New.primeRemainder d q (Real.exp v) : ℂ) *
        Complex.exp ((1 - s) * (v : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _hv
      rw [centeredSmoothing_div_eq_primeRemainder d q (Real.exp v) (Real.exp_ne_zero v)]
    _ = _ := New.integral_primeRemainder hd hcop hs

/-- The meromorphic continuation and residues also belong to the actual
native weighted profile, by the exact normalization identity. -/
theorem isPolar_centeredSmoothing_div_exp (d : ℕ) [Fact d.Prime]
    (q : ℕ) [NeZero q] (hd : d % 8 = 7) (hcop : q.Coprime d) :
    New.IsPolar
      (fun v : ℝ =>
        centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
          (-(New.logDerivMean d q 1).re) (Real.exp v) / Real.exp v)
      (fun s : ℂ =>
        (∑ ψ : DirichletCharacter ℂ q,
          (analyticOrderNatAt (New.entireL ψ) s -
            analyticOrderNatAt (New.entireL (New.quadTwist ψ d)) s : ℂ)) /
          (Nat.totient q : ℂ) / (s * (1 - s))) := by
  have heq : (fun v : ℝ =>
      centeredSmoothing (New.lambdaKResidueClass d q) (Nat.totient q : ℝ)⁻¹
        (-(New.logDerivMean d q 1).re) (Real.exp v) / Real.exp v) =
      (fun v : ℝ => New.primeRemainder d q (Real.exp v)) := by
    funext v
    exact centeredSmoothing_div_eq_primeRemainder d q (Real.exp v) (Real.exp_ne_zero v)
  rw [heq]
  exact New.isPolar_primeRemainder hd hcop

end InfoGeometry.GRHIntegration
