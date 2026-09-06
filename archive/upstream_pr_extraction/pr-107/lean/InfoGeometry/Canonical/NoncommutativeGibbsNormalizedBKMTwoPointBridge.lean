import InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge

/-!
# Normalized Duhamel two-point function as a Kubo--Mori pairing

For the native faithful Gibbs density `rho = Z⁻¹ exp H`, the preceding CFC
power theorem converts the Kubo--Mori kernel into the normalized Duhamel
kernel.  The sole orientation change is interval reflection `s ↦ 1 - s`.

This owner proves the normalized two-point identification, not a Hessian.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge

open MeasureTheory
open scoped Interval
open SouriauOnsagerBKM
open SouriauOnsagerBKM.FaithfulDensityOperator
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsDuhamelTwoPointBridge
open InfoGeometry.Canonical.NoncommutativeGibbsRpowNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/-- The traced complex Fréchet response normalized by the real partition. -/
noncomputable def normalizedFrechetTwoPoint
    {n : ℕ} (H A B : Operator n) : ℂ :=
  (gibbsPartitionReal H)⁻¹ *
    finiteOperatorTrace
      (exponentialDerivative (𝕜 := ℂ) H A * B)

/-- Pointwise identification with the reflected normalized Duhamel kernel. -/
theorem faithfulGibbs_kuboMoriIntegrand_star_eq_reflectedDuhamel
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (s : ℝ) :
    (faithfulGibbsDensity H hH hZ).kuboMoriIntegrand
        (star A) B s =
      ((gibbsPartitionReal H)⁻¹ : ℂ) *
        finiteOperatorTrace
          (NormedSpace.exp (s • H) *
            A *
              NormedSpace.exp ((1 - s) • H) *
                B) := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  simp only [star_star]
  rw [faithfulGibbsDensity_rpow H hH hZ s]
  rw [faithfulGibbsDensity_rpow H hH hZ (1 - s)]
  let Z : ℝ := gibbsPartitionReal H
  let c : ℝ := Z⁻¹
  have hc : 0 < c := inv_pos.mpr hZ
  have hpow (t : ℝ) : Z ^ (-t) = c ^ t := by
    symm
    simpa [Z, c, normalizedScalarGibbsWeight] using
      normalizedScalarGibbsWeight_rpow Z 0 t hZ
  rw [hpow s, hpow (1 - s)]
  have hscale :
      (c ^ s • NormedSpace.exp (s • H)) *
            A *
            (c ^ (1 - s) • NormedSpace.exp ((1 - s) • H)) *
            B =
        (c ^ s * c ^ (1 - s)) •
          (NormedSpace.exp (s • H) *
            A *
              NormedSpace.exp ((1 - s) • H) *
                B) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  change finiteOperatorTrace
      ((c ^ s • NormedSpace.exp (s • H)) *
        A *
        (c ^ (1 - s) • NormedSpace.exp ((1 - s) • H)) *
        B) = _
  rw [hscale]
  change finiteOperatorTrace
      (((c ^ s * c ^ (1 - s) : ℝ) : ℂ) •
        (NormedSpace.exp (s • H) *
          A *
            NormedSpace.exp ((1 - s) • H) *
              B)) = _
  rw [finiteOperatorTrace_complex_smul]
  rw [← Real.rpow_add hc]
  have hs : s + (1 - s) = 1 := by ring
  rw [hs, Real.rpow_one]
  rfl

/-- The Kubo--Mori pairing is the normalized Duhamel two-point integral. -/
theorem faithfulGibbs_kuboMoriPairing_star_eq_normalizedDuhamel
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) :
    (faithfulGibbsDensity H hH hZ).kuboMoriPairing
        (star A) B =
      ((gibbsPartitionReal H)⁻¹ : ℂ) *
        ∫ s in (0 : ℝ)..1,
          finiteOperatorTrace
            (NormedSpace.exp ((1 - s) • H) *
              A *
                NormedSpace.exp (s • H) *
                  B) := by
  unfold FaithfulDensityOperator.kuboMoriPairing
  simp_rw [
    faithfulGibbs_kuboMoriIntegrand_star_eq_reflectedDuhamel
      H hH hZ A B]
  rw [intervalIntegral.integral_const_mul]
  let f : ℝ → ℂ := fun s =>
    finiteOperatorTrace
      (NormedSpace.exp (s • H) *
        A *
          NormedSpace.exp ((1 - s) • H) *
            B)
  have hreflect :
      (∫ s in (0 : ℝ)..1, f s) =
        ∫ s in (0 : ℝ)..1, f (1 - s) := by
    symm
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := (1 : ℝ)) f 1)
  rw [hreflect]
  rfl

/-- Final normalized Fréchet--Kubo--Mori two-point identification. -/
theorem normalizedFrechetTwoPoint_eq_kuboMoriPairing
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) :
    normalizedFrechetTwoPoint H A B =
      (faithfulGibbsDensity H hH hZ).kuboMoriPairing
        (star A) B := by
  unfold normalizedFrechetTwoPoint
  rw [trace_complexExponentialDerivative_mul_eq_duhamelTwoPoint]
  exact
    (faithfulGibbs_kuboMoriPairing_star_eq_normalizedDuhamel
      H hH hZ A B).symm

end InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge
